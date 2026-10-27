module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B3Abar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B2Ind

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace B89

open Subgroup CFSG.Blueprint

theorem conj_mem_of_odd {Γ : Type*} [Group Γ] {Ab : Subgroup Γ} {u h a a'' : Γ}
    (hu : u * u = 1) (hcomm : ∀ x ∈ Ab, x * u = u * x) (hnot : u ∉ Ab) (hodd : Odd (orderOf a))
    (ha'' : a'' ∈ Ab) (hform : h * a * h⁻¹ = a'' ∨ h * a * h⁻¹ = u * a'') :
    h * a * h⁻¹ ∈ Ab := by
  rcases hform with h1 | h1
  · rw [h1]
    exact ha''
  · exfalso
    apply hnot
    have h2 : (h * a * h⁻¹) ^ orderOf a = 1 := by
      rw [conj_pow, pow_orderOf_eq_one]
      group
    rw [h1, Commute.mul_pow (show Commute u a'' from (hcomm a'' ha'').symm)] at h2
    have h3 : u ^ orderOf a = u := by
      obtain ⟨k, hk⟩ := hodd
      rw [hk, pow_succ, pow_mul, sq, hu, one_pow, one_mul]
    rw [h3] at h2
    rw [eq_inv_of_mul_eq_one_left h2]
    exact Ab.inv_mem (Ab.pow_mem ha'' _)

theorem conj_mem_of_forall_odd {Γ : Type*} [Group Γ] {Ab : Subgroup Γ} {h : Γ}
    (hAb : Nonempty (↥Ab ≃* alternatingGroup (Fin 6)))
    (hodd : ∀ a ∈ Ab, Odd (orderOf a) → h * a * h⁻¹ ∈ Ab) : ∀ a ∈ Ab, h * a * h⁻¹ ∈ Ab := by
  obtain ⟨e⟩ := hAb
  let W : Subgroup ↥Ab := (Ab.comap (MulAut.conj h).toMonoidHom).comap Ab.subtype
  have hW : ∀ a : ↥Ab, a ∈ W ↔ h * (a : Γ) * h⁻¹ ∈ Ab := fun a => by
    show (MulAut.conj h) (a : Γ) ∈ Ab ↔ h * (a : Γ) * h⁻¹ ∈ Ab
    rw [MulAut.conj_apply]
  let Wt : Subgroup (alternatingGroup (Fin 6)) := W.comap e.symm.toMonoidHom
  let W' : Subgroup (Equiv.Perm (Fin 6)) := Wt.map (alternatingGroup (Fin 6)).subtype
  have h3 : ∀ σ : Equiv.Perm (Fin 6), σ.IsThreeCycle → σ ∈ W' := by
    intro σ hσ
    have hσA : σ ∈ alternatingGroup (Fin 6) := hσ.mem_alternatingGroup
    refine ⟨⟨σ, hσA⟩, ?_, rfl⟩
    show e.symm ⟨σ, hσA⟩ ∈ W
    rw [hW]
    apply hodd _ (e.symm ⟨σ, hσA⟩).2
    have h4 : orderOf ((e.symm ⟨σ, hσA⟩ : ↥Ab) : Γ) = 3 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hσ.orderOf
    rw [h4]
    decide
  have h5 : alternatingGroup (Fin 6) ≤ W' := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    exact fun σ hσ => h3 σ hσ
  intro a ha
  have h6 : e ⟨a, ha⟩ ∈ Wt := by
    obtain ⟨w, hw, hw'⟩ := h5 (e ⟨a, ha⟩).2
    have : w = e ⟨a, ha⟩ := Subtype.ext hw'
    rwa [this] at hw
  have h7 : (⟨a, ha⟩ : ↥Ab) ∈ W := by
    have := h6
    simpa [Wt] using this
  exact (hW _).mp h7

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

theorem zpowers_t_cases (hctx : Sec8Ctx G t L S z g B) {s : G} (hs : s ∈ zpowers t) :
    s = 1 ∨ s = t := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have h2 : orderOf t = 2 := hctx.toSec3SettingLB.involution
  have h3 : t ^ (i % (orderOf t : ℤ)) = t ^ i := zpow_mod_orderOf t i
  rw [h2] at h3
  push_cast at h3
  rcases Int.emod_two_eq_zero_or_one i with h | h
  · left
    rw [← h3, h]
    simp
  · right
    rw [← h3, h]
    simp

theorem mem_cent_A_of {c : G} (hct : c * t = t * c) (hcB : ∀ b ∈ B, c * b = b * c) :
    c ∈ centralizer (Asub8 t B : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hAc : Asub8 t B ≤ centralizer ({c} : Set G) := by
    rw [Asub8]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hct.symm
    · intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcB b hb).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hAc ha)

theorem rhoG_of_cent_A (h8A : Asc82Lemma8A) (hE : Sec8E G t L S z g B E) {c : G}
    (hc : c ∈ centralizer (Asub8 t B : Set G)) : rhoG hE c = 1 ∨ rhoG hE c = rhoG hE t := by
  have hctx := hE.ctx
  have hcAO : c ∈ Asub8 t B ⊔ oddCoreIn (Nsub8 t B) := by
    rw [← sec8t84a1_centA h8A hctx]
    exact hc
  have hAO : ∀ x ∈ Asub8 t B, ∀ y ∈ oddCoreIn (Nsub8 t B), x * y = y * x :=
    fun x hx y hy => (O_comm_A h8A hctx hy hx).symm
  obtain ⟨a, ha, o, ho, rfl⟩ := A3.exists_mul_of_comm hAO hcAO
  have hzB : ∀ x ∈ zpowers t, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have h1 : zpowers t ≤ centralizer ({y} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (sec8t84a1_t_comm hctx hy)
    exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hx)
  obtain ⟨s, hs, b, hb, rfl⟩ := A3.exists_mul_of_comm hzB (show a ∈ zpowers t ⊔ B from ha)
  have hsN : s ∈ Nsub8 t B := sec8t84a1_A_le_N (Subgroup.mem_sup_left hs)
  have hbN : b ∈ Nsub8 t B := sec8t84a1_A_le_N (sec8t84a1_B_le_A hb)
  have hoN : o ∈ Nsub8 t B := (oddCoreIn_normal (Nsub8 t B)).1 ho
  rw [rhoG_mul hE ((Nsub8 t B).mul_mem hsN hbN) hoN, rhoG_mul hE hsN hbN,
    rhoG_of_mem_E hE (B_le_E hE hb), rhoG_of_mem_O hE ho, mul_one, mul_one]
  rcases zpowers_t_cases hctx hs with rfl | rfl
  · left
    exact rhoG_one hE
  · right
    rfl

theorem rhoG_conj_odd (F : Sec8T84Base) (hE : Sec8E G t L S z g B E)
    (hnorm : ∀ h ∈ autIn (centralizer ({t} : Set G)) B, ∀ a ∈ autIn L B,
      h * a * h⁻¹ ∈ autIn L B)
    {x : G} (hx : x ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G))
    {a : MulAut ↥E} (ha : a ∈ Abar hE) (hodd : Odd (orderOf a)) :
    rhoG hE x * a * (rhoG hE x)⁻¹ ∈ Abar hE := by
  have hctx := hE.ctx
  obtain ⟨m, hmL, hmB, rfl⟩ := exists_of_mem_Abar hE ha
  have hxN : x ∈ Nsub8 t B := XCt_le_N hE hx
  have hxB : x ∈ normalizer (B : Set G) := XCt_le_NB hE hx
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.toSec3SettingLB.component.le
  have hmN : m ∈ Nsub8 t B := (sec8t84a1_L_norm_le hctx ⟨hmL, hmB⟩).1
  have hIx := induces_conjAut B hxB
  have hIm := induces_conjAut B hmB
  have hαx : sec1011_conjAut B x hxB ∈ autIn (centralizer ({t} : Set G)) B :=
    sec1011_conjAut_mem hx.2 hxB
  have hαm : sec1011_conjAut B m hmB ∈ autIn L B := sec1011_conjAut_mem hmL hmB
  have hβ := hnorm _ hαx _ hαm
  obtain ⟨m'', hm''L, hIm''⟩ := exists_induces hβ
  have hm''B : m'' ∈ normalizer (B : Set G) := hIm''.mem_normalizer
  have hm''N : m'' ∈ Nsub8 t B := (sec8t84a1_L_norm_le hctx ⟨hm''L, hm''B⟩).1
  have hIc : Induces B (x * m * x⁻¹ * m''⁻¹) 1 := by
    have h1 := ((hIx.mul hIm).mul hIx.inv).mul hIm''.inv
    rwa [mul_inv_cancel] at h1
  have hcB : ∀ b ∈ B, (x * m * x⁻¹ * m''⁻¹) * b = b * (x * m * x⁻¹ * m''⁻¹) := by
    intro b hb
    have h2 : (b : G) = (x * m * x⁻¹ * m''⁻¹) * b * (x * m * x⁻¹ * m''⁻¹)⁻¹ := hIc ⟨b, hb⟩
    calc (x * m * x⁻¹ * m''⁻¹) * b
        = ((x * m * x⁻¹ * m''⁻¹) * b * (x * m * x⁻¹ * m''⁻¹)⁻¹) * (x * m * x⁻¹ * m''⁻¹) := by
          group
      _ = b * (x * m * x⁻¹ * m''⁻¹) := by rw [← h2]
  have hcC : x * m * x⁻¹ * m''⁻¹ ∈ centralizer ({t} : Set G) :=
    mul_mem (mul_mem (mul_mem hx.2 (hLt hmL)) (inv_mem hx.2)) (inv_mem (hLt hm''L))
  have hcA := mem_cent_A_of (Subgroup.mem_centralizer_singleton_iff.mp hcC) hcB
  have hcN : x * m * x⁻¹ * m''⁻¹ ∈ Nsub8 t B :=
    Subgroup.centralizer_le_normalizer (Asub8 t B : Set G) hcA
  have hxmx : x * m * x⁻¹ = (x * m * x⁻¹ * m''⁻¹) * m'' := by group
  have hconj : rhoG hE x * rhoG hE m * (rhoG hE x)⁻¹ =
      rhoG hE (x * m * x⁻¹ * m''⁻¹) * rhoG hE m'' := by
    rw [← rhoG_conj hE hxN hmN, hxmx, rhoG_mul hE hcN hm''N]
    congr 2
    group
  have hcho := rhoG_of_cent_A F.h8A hE hcA
  refine conj_mem_of_odd (Ab := Abar hE) (u := rhoG hE t) (h := rhoG hE x) (a := rhoG hE m)
    (a'' := rhoG hE m'') (rhoG_t_mul_self hE) (fun y hy => Abar_comm_u hE hy)
    (u_not_mem_Abar F hE) hodd (rhoG_mem_Abar hE hm''L hm''B) ?_
  rcases hcho with h | h
  · left
    rw [hconj, h, one_mul]
  · right
    rw [hconj, h]

theorem rhoG_conj_mem_Abar (F : Sec8T84Base) (hE : Sec8E G t L S z g B E)
    (hnorm : ∀ h ∈ autIn (centralizer ({t} : Set G)) B, ∀ a ∈ autIn L B,
      h * a * h⁻¹ ∈ autIn L B)
    {x : G} (hx : x ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G))
    {a : MulAut ↥E} (ha : a ∈ Abar hE) : rhoG hE x * a * (rhoG hE x)⁻¹ ∈ Abar hE :=
  conj_mem_of_forall_odd (Abar_equiv_A6 F hE)
    (fun a ha hodd => rhoG_conj_odd F hE hnorm hx ha hodd) a ha

end B89

end CFSG.OddStandard.SmallF3.Omega
