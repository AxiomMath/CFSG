module

public import CFSG.LargeExtraspecial.S11Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_of_two_points (hy : Hyp S g) {k j u : G}
    (hkQ : k * S.z * k⁻¹ ∈ S.QG) (hkz : k * S.z * k⁻¹ ≠ S.z)
    (hjQ : j * S.z * j⁻¹ ∈ S.QG) (hjz : j * S.z * j⁻¹ ≠ S.z)
    (hjk : j * S.z * j⁻¹ ≠ k * S.z * k⁻¹) (hjk' : j * S.z * j⁻¹ ≠ k * S.z * k⁻¹ * S.z)
    (huM : u * S.z * u⁻¹ ∈ S.M) (huQ : u * S.z * u⁻¹ ∉ S.QG)
    (huk : u * S.z * u⁻¹ ∈ S.Qa k) (huj : u * S.z * u⁻¹ ∈ S.Qa j) :
    Timmesfeld11_1Stmt S := by
  refine ⟨k, u, huM, hkQ, hkz, huQ, huk, fun hR => ?_⟩
  have hyk := hy.of_conj hkQ hkz
  obtain ⟨m, hm, hmk⟩ := hyk.fusion j hjQ hjz
  have hc : ((⟨m, hm⟩ : S.M) : G) * k * S.z * (((⟨m, hm⟩ : S.M) : G) * k)⁻¹ =
      j * S.z * j⁻¹ := by
    rw [mul_conj_z S]
    exact hmk
  have ht : S.ρ ⟨u * S.z * u⁻¹, huM⟩ ∈ S.Lbar (((⟨m, hm⟩ : S.M) : G) * k) := by
    rw [S.Lbar_eq_of_conj_eq hc]
    exact S.ρ_mem_Lbar (y := u * S.z * u⁻¹) ⟨huj, huM⟩
  have hV := Vt_le_span_of_Rbar_eq hyk.hyp4 hyk.cons hR (cl_mem_Vt ht)
  rw [hc] at hV
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hV
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases r with rfl | rfl
  · exact S.cl_conj_z_ne_zero hjQ hjz (by rw [← hr, zero_smul])
  · rw [one_smul] at hr
    rcases (S.cl_eq_cl_iff hkQ hjQ).mp hr with h | h
    · exact hjk h
    · exact hjk' h

variable (S) in
structure IncClosed (A : Subgroup G) : Prop where
  le_QG : A ≤ S.QG
  z_mem : S.z ∈ A
  conj : ∀ x ∈ A, x ≠ 1 → ∃ k : G, x = k * S.z * k⁻¹
  le_Qa : ∀ k : G, k * S.z * k⁻¹ ∈ A → A ≤ S.Qa k

variable (S g) in
structure Cfg111 (A : Subgroup G) : Prop where
  hy : Hyp S g
  irr : ¬ S.IsReducible
  exT : ∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g
  not111 : ¬ Timmesfeld11_1Stmt S
  inc : IncClosed S A
  mem : g * S.z * g⁻¹ ∈ A
  max : ∀ B : Subgroup G, IncClosed S B → g * S.z * g⁻¹ ∈ B → Nat.card B ≤ Nat.card A

omit [Finite G] in
theorem mem_map_conj_iff {A : Subgroup G} {h x : G} :
    x ∈ A.map (MulAut.conj h).toMonoidHom ↔ h⁻¹ * x * h ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨h⁻¹ * x * h, hx, by simp [mul_assoc]⟩

omit [Finite G] in
theorem card_map_conj (A : Subgroup G) (h : G) :
    Nat.card (A.map (MulAut.conj h).toMonoidHom) = Nat.card A :=
  card_map_of_injective (MulAut.conj h).injective

omit [Finite G] in
theorem map_conj_inv_map_conj (A : Subgroup G) (h : G) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom = A := by
  ext x
  rw [mem_map_conj_iff, mem_map_conj_iff]
  simp [mul_assoc]

theorem mem_Qa_iff_conj (k x : G) : x ∈ S.Qa k ↔ k⁻¹ * x * k ∈ S.QG := by
  have h := mem_Qa_mul_iff S (h := k) (g := 1) (x := x)
  rwa [mul_one, S.Qa_one] at h

theorem QG_inf_Qa_eq_of_mul_z {k k' : G} (hkQ : k * S.z * k⁻¹ ∈ S.QG)
    (hkz : k * S.z * k⁻¹ ≠ S.z) (h : k' * S.z * k'⁻¹ = k * S.z * k⁻¹ * S.z) :
    S.QG ⊓ S.Qa k' = S.QG ⊓ S.Qa k := by
  obtain ⟨q, hq, hqk⟩ := S.exists_mul_conj_eq_mul_z hkQ hkz
  rw [S.Qa_eq_of_conj_eq (h.trans hqk.symm), S.QG_inf_Qa_mul_of_mem_QG hkQ hkz hq]

omit [Finite G] in
theorem commute_of_mem_Qa {k x : G} (hx : x ∈ S.Qa k) :
    x * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * x :=
  mem_centralizer_singleton_iff.mp ((S.conjBy k).QG_le_M hx)

namespace IncClosed

variable {A : Subgroup G}

omit [Finite G] in
theorem mul_self (hA : IncClosed S A) {x : G} (hx : x ∈ A) : x * x = 1 := by
  by_cases hx1 : x = 1
  · rw [hx1, one_mul]
  obtain ⟨k, rfl⟩ := hA.conj x hx hx1
  exact (S.conjBy k).z_mul_z

omit [Finite G] in
theorem map_conj (hA : IncClosed S A) {h : G} (hh : h ∈ S.M) :
    IncClosed S (A.map (MulAut.conj h).toMonoidHom) where
  le_QG := by
    rintro _ ⟨x, hx, rfl⟩
    exact S.conj_mem_QG hh (hA.le_QG hx)
  z_mem := by
    rw [mem_map_conj_iff]
    rw [S.z_comm (S.M.inv_mem hh), mul_assoc, inv_mul_cancel, mul_one]
    exact hA.z_mem
  conj := by
    rintro _ ⟨x, hx, rfl⟩ hx1
    have hx1' : x ≠ 1 := fun h1 => hx1 (by rw [h1]; simp)
    obtain ⟨k, rfl⟩ := hA.conj x hx hx1'
    exact ⟨h * k, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  le_Qa := by
    intro k hk
    rw [mem_map_conj_iff] at hk
    have hk' : (h⁻¹ * k) * S.z * (h⁻¹ * k)⁻¹ ∈ A := by
      convert hk using 1
      group
    have h1 := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) (hA.le_Qa _ hk')
    rwa [← Qa_mul, mul_inv_cancel_left] at h1

end IncClosed

theorem Dset_map_conj (k : S.M) (t : S.O) :
    Dset S g (S.ρ k * t * (S.ρ k)⁻¹) =
      (fun X => X.map (MulAut.conj (S.ρ k)).toMonoidHom) '' Dset S g t := by
  have e : ∀ h : S.M, (S.Lbar (((k⁻¹ * h : S.M) : G) * g)).map
      (MulAut.conj (S.ρ k)).toMonoidHom = S.Lbar ((h : G) * g) := fun h => by
    rw [← Lbar_mul S k]
    congr 1
    simp [mul_assoc]
  ext X
  constructor
  · rintro ⟨h, rfl, hτ⟩
    refine ⟨S.Lbar (((k⁻¹ * h : S.M) : G) * g), ⟨k⁻¹ * h, rfl, ?_⟩, e h⟩
    rw [← e h] at hτ
    obtain ⟨t', ht', htt⟩ := hτ
    have : t' = t := by
      simpa [MulAut.conj_apply] using htt
    rwa [← this]
  · rintro ⟨_, ⟨h, rfl, ht⟩, rfl⟩
    refine ⟨k * h, ?_, ⟨t, ht, rfl⟩⟩
    rw [← e (k * h)]
    congr 2
    simp

theorem Rbar_map_conj (k : S.M) (t : S.O) :
    Rbar S g (S.ρ k * t * (S.ρ k)⁻¹) = (Rbar S g t).map (MulAut.conj (S.ρ k)).toMonoidHom := by
  rw [Rbar, Rbar, Dset_map_conj, sSup_image, ← (Subgroup.gc_map_comap _).l_sSup]

theorem exT_mul {h : G} (hh : h ∈ S.M) (hT : ∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) :
    ∃ t ∈ S.Lbar (h * g), t ≠ 1 ∧ Rbar S (h * g) t ≠ S.Lbar (h * g) := by
  obtain ⟨t, ht, ht1, hR⟩ := hT
  set h' : S.M := ⟨h, hh⟩
  refine ⟨S.ρ h' * t * (S.ρ h')⁻¹, conj_mem_Lbar_mul S h' ht, fun h1 => ht1 ?_, fun hR' => ?_⟩
  · have := congrArg (fun x => (S.ρ h')⁻¹ * x * S.ρ h') h1
    simpa [mul_assoc] using this
  · apply hR
    have e : Rbar S ((h' : G) * g) (S.ρ h' * t * (S.ρ h')⁻¹) = S.Lbar ((h' : G) * g) := hR'
    rw [Rbar_mul, Rbar_map_conj, Lbar_mul S h'] at e
    exact Subgroup.map_injective (MulAut.conj (S.ρ h')).injective e

theorem Cfg111.conj {A : Subgroup G} (C : Cfg111 S g A) {h : G} (hh : h ∈ S.M) :
    Cfg111 S (h * g) (A.map (MulAut.conj h).toMonoidHom) where
  hy := C.hy.of_conj (conj_mem_QG' S hh C.hy.hyp4.conj_mem) (conj_ne_z' S hh C.hy.hyp4.conj_ne)
  irr := C.irr
  exT := exT_mul hh C.exT
  not111 := C.not111
  inc := C.inc.map_conj hh
  mem := by
    rw [mem_map_conj_iff]
    convert C.mem using 1
    group
  max := fun B hB hgB => by
    have hmem : g * S.z * g⁻¹ ∈ B.map (MulAut.conj h⁻¹).toMonoidHom := by
      rw [mem_map_conj_iff]
      convert hgB using 1
      group
    have := C.max _ (hB.map_conj (S.M.inv_mem hh)) hmem
    rwa [card_map_conj, ← card_map_conj A h] at this

end CFSG.LargeExtraspecial.S11
