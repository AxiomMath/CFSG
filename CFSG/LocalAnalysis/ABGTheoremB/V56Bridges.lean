module

public import CFSG.LocalAnalysis.ABGTheoremB.V56Inputs
public import CFSG.LocalAnalysis.ABGTheoremB.IVNFacts
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.NFacts
import CFSG.LocalAnalysis.ABGTheoremB.V3
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.ABGTheoremB.V4Defs

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

universe u

section General

variable {G : Type u} [Group G]

private theorem eq_one_of_mem_of_pow_two_pow {O : Subgroup G} (hO : Odd (Nat.card O)) {g : G}
    (hg : g ∈ O) {k : ℕ} (hk : g ^ (2 ^ k) = 1) : g = 1 := by
  have hodd : Odd (orderOf g) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hg)
  have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  exact orderOf_eq_one_iff.mp (((Nat.coprime_two_right.mpr hodd).pow_right k).eq_one_of_dvd h2)

private theorem mem_of_sq_mem_of_odd {H : Subgroup G} {x : G} (hx : Odd (orderOf x))
    (h : x ^ 2 ∈ H) : x ∈ H := by
  obtain ⟨k, hk⟩ := hx
  have hx1 : x ^ (2 * (k + 1)) = x := by
    rw [show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [← hx1, pow_mul]
  exact H.pow_mem h _

private theorem mem_of_pow_two_pow_mem_of_odd {H : Subgroup G} {x : G} (hx : Odd (orderOf x))
    (k : ℕ) (h : x ^ 2 ^ k ∈ H) : x ∈ H := by
  induction k generalizing x with
  | zero => simpa using h
  | succ k ih =>
    apply mem_of_sq_mem_of_odd hx
    apply ih (hx.of_dvd_nat (orderOf_pow_dvd 2))
    rwa [← pow_mul, ← pow_succ']

private theorem exists_pow_mem_of_mem_sup {p : ℕ} {A P : Subgroup G} (hP : IsPGroup p P)
    (hPA : P ≤ Subgroup.normalizer (A : Set G)) {b : G} (hb : b ∈ A ⊔ P) :
    ∃ k : ℕ, b ^ (p ^ k) ∈ A := by
  have hb' : b ∈ ((A ⊔ P : Subgroup G) : Set G) := hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A P hPA] at hb'
  obtain ⟨a, ha, t, ht, rfl⟩ := hb'
  have key : ∀ m : ℕ, ∃ a' ∈ A, (a * t) ^ m = a' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, A.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨a', ha', hm⟩ := ih
      refine ⟨a' * (t ^ m * a * (t ^ m)⁻¹), A.mul_mem ha' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hPA (P.pow_mem ht m)) a).mp ha
      · rw [pow_succ, hm, pow_succ]
        group
  obtain ⟨k, hk⟩ := hP ⟨t, ht⟩
  have hk' : t ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨a', ha', h⟩ := key (p ^ k)
  refine ⟨k, ?_⟩
  rw [h, hk', mul_one]
  exact ha'

private theorem normalizer_le_normalizer_centralizer' [Finite G] (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
  intro n hn
  apply Subgroup.mem_normalizer_fintype
  intro c hc
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc ⊢
  intro r hr
  have hrn : n⁻¹ * r * n ∈ R := by
    have h := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (R : Set G)).inv_mem hn)
      r).mp hr
    simpa using h
  have h := hc _ hrn
  calc r * (n * c * n⁻¹) = n * ((n⁻¹ * r * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * r * n)) * n⁻¹ := by rw [h]
    _ = n * c * n⁻¹ * r := by group

private theorem normalizer_le_normalizer_oddCoreIn' [Finite G] (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (oddCoreIn H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hle : (oddCoreIn H).map (MulAut.conj g).toMonoidHom ≤ oddCoreIn H := by
    apply le_oddCoreIn
    · exact (Subgroup.map_mono (oddCoreIn_le H)).trans hg.le
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact hg.ge.trans (Subgroup.map_mono (le_normalizer_oddCoreIn H))
    · rw [Subgroup.card_map_of_injective hinj]
      exact odd_card_oddCoreIn H
  exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective hinj).ge

private theorem exists_inv_mul_mem_centralizer [Finite G] {A M : Subgroup G} (hA : IsPGroup 2 A)
    (hM : Odd (Nat.card M)) (hAM : A ≤ Subgroup.normalizer (M : Set G)) {g : G}
    (hg : ∀ a ∈ A, g * a * g⁻¹ * a⁻¹ ∈ M) :
    ∃ m ∈ M, m⁻¹ * g ∈ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := M ⊔ A with hH
  have hAH : A ≤ H := le_sup_right
  have hAs : IsSylowOf 2 A H := by
    rw [isSylowOf_iff]
    refine ⟨hAH, hA, ?_⟩
    rw [hH, relIndex_sup_eq_relIndex_of_le_normalizer hAM]
    intro h2
    have h2' := h2.trans (Subgroup.relIndex_dvd_card A M)
    exact (Nat.not_even_iff_odd.mpr hM) (even_iff_two_dvd.mpr h2')
  have hAg : IsSylowOf 2 (A.map (MulAut.conj g).toMonoidHom) H := by
    apply isSylowOf_of_card
    · rintro _ ⟨a, ha, rfl⟩
      have : (MulAut.conj g).toMonoidHom a = (g * a * g⁻¹ * a⁻¹) * a := by
        simp [MulAut.conj_apply]
      rw [this]
      exact H.mul_mem (Subgroup.mem_sup_left (hg a ha)) (hAH ha)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hAs.card_eq]
  obtain ⟨k, hk, hkA⟩ := hAs.exists_mem_conj hAg
  have hk' : k ∈ ((M ⊔ A : Subgroup G) : Set G) := hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left M A hAM] at hk'
  obtain ⟨m, hm, a₀, ha₀, hma⟩ := hk'
  have hma : m * a₀ = k := hma
  refine ⟨m, hm, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 : (m⁻¹ * g) * a * (m⁻¹ * g)⁻¹ ∈ A := by
    have hx := (hkA (g * a * g⁻¹)).mp ⟨a, ha, by simp [MulAut.conj_apply]⟩
    rw [← hma] at hx
    have : (m⁻¹ * g) * a * (m⁻¹ * g)⁻¹ =
        a₀ * ((m * a₀)⁻¹ * (g * a * g⁻¹) * (m * a₀)) * a₀⁻¹ := by group
    rw [this]
    exact A.mul_mem (A.mul_mem ha₀ hx) (A.inv_mem ha₀)
  have h2 : (m⁻¹ * g) * a * (m⁻¹ * g)⁻¹ * a⁻¹ ∈ M := by
    have : (m⁻¹ * g) * a * (m⁻¹ * g)⁻¹ * a⁻¹ = m⁻¹ * (g * a * g⁻¹ * a⁻¹) * (a * m * a⁻¹) := by
      group
    rw [this]
    exact M.mul_mem (M.mul_mem (M.inv_mem hm) (hg a ha))
      ((Subgroup.mem_normalizer_iff.mp (hAM ha) m).mp hm)
  have h3 : (m⁻¹ * g) * a * (m⁻¹ * g)⁻¹ * a⁻¹ ∈ A := A.mul_mem h1 (A.inv_mem ha)
  obtain ⟨k₂, hk₂⟩ := hA ⟨_, h3⟩
  have hk₂' : ((m⁻¹ * g) * a * (m⁻¹ * g)⁻¹ * a⁻¹) ^ (2 ^ k₂) = 1 := by
    simpa using congrArg Subtype.val hk₂
  have h4 := eq_one_of_mem_of_pow_two_pow hM h2 hk₂'
  rw [mul_inv_eq_one] at h4
  calc a * (m⁻¹ * g) = (m⁻¹ * g) * a * (m⁻¹ * g)⁻¹ * (m⁻¹ * g) := by rw [h4]
    _ = (m⁻¹ * g) * a := by group

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

private theorem D_le_normalizer_C : σ.D ≤ Subgroup.normalizer (σ.C : Set G) :=
  inf_le_right.trans (normalizer_le_normalizer_centralizer' σ.T)

private theorem D_le_normalizer_oddCoreIn_C :
    σ.D ≤ Subgroup.normalizer (oddCoreIn σ.C : Set G) :=
  σ.D_le_normalizer_C.trans (normalizer_le_normalizer_oddCoreIn' σ.C)

theorem oddCoreIn_C_sup_eq (hN : σ.IVNFacts) :
    oddCoreIn σ.C ⊔ (σ.D ⊓ Subgroup.centralizer (σ.T : Set G)) = σ.C := by
  refine le_antisymm (sup_le (oddCoreIn_le σ.C) inf_le_right) fun c hc => ?_
  have hc' : c ∈ ((oddCoreIn σ.C ⊔ σ.D : Subgroup G) : Set G) := hN.C_le_oddCore_sup_D hc
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ σ.D_le_normalizer_oddCoreIn_C] at hc'
  obtain ⟨o, ho, f, hf, hof⟩ := hc'
  have hof : o * f = c := hof
  have hfC : f ∈ σ.C := by
    have : f = o⁻¹ * c := by rw [← hof]; group
    rw [this]
    exact σ.C.mul_mem (σ.C.inv_mem (oddCoreIn_le σ.C ho)) hc
  rw [← hof]
  exact Subgroup.mul_mem_sup ho ⟨hf, hfC⟩

private theorem C_inf_ON_le_oddCoreIn_C : σ.C ⊓ σ.ON ≤ oddCoreIn σ.C := by
  apply le_oddCoreIn inf_le_left
  · exact (le_inf Subgroup.le_normalizer (σ.C_le_N.trans σ.N_le_normalizer_ON)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  · exact σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)

private theorem covers (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts)
    {J : Subgroup G} (hJ : σ.IsV21Layer J) {W : Subgroup G} (hW : W ∈ σ.familyW J)
    (hWO : W ≤ oddCoreIn σ.C) :
    ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
      ((W ⊔ σ.D : Subgroup G) : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G) := by
  intro c hc
  obtain ⟨hcC, hcL⟩ := Subgroup.mem_inf.mp hc
  set M : Subgroup G := pCoreIn σ.p σ.N with hMdef
  have hJN : J ≤ σ.N := hJ.le.trans hσ.L₀_le_N
  have hMJ : M ≤ J := hJ.pCore_le
  have hMO : M ≤ σ.ON := by
    rw [hMdef, ← hJ.inf_eq]
    exact inf_le_right
  have hNM : σ.N ≤ Subgroup.normalizer (M : Set G) := le_normalizer_map_subtype σ.N _
  have hModd : Odd (Nat.card M) := σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le hMO)
  have hF₀2 : IsPGroup 2 (σ.D ⊓ Subgroup.centralizer (σ.T : Set G) : Subgroup G) :=
    σ.S.isPGroup'.to_le (inf_le_left.trans σ.D_le_S)
  have hc' : c ∈ ((oddCoreIn σ.C ⊔ σ.D : Subgroup G) : Set G) := hN.C_le_oddCore_sup_D hcC
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ σ.D_le_normalizer_oddCoreIn_C] at hc'
  obtain ⟨o, ho, f, hfD, hof⟩ := hc'
  have hof : o * f = c := hof
  have hfC : f ∈ σ.C := by
    have : f = o⁻¹ * c := by rw [← hof]; group
    rw [this]
    exact σ.C.mul_mem (σ.C.inv_mem (oddCoreIn_le σ.C ho)) hcC
  have hfL : f ∈ σ.L := by
    rw [hII.L_eq]
    exact Subgroup.mem_sup_right ⟨hfD, hfC⟩
  have hfN : f ∈ σ.N := σ.D_le_N hσ hfD
  have hoL : o ∈ σ.L := by
    have : o = c * f⁻¹ := by rw [← hof]; group
    rw [this]
    exact σ.L.mul_mem hcL (σ.L.inv_mem hfL)
  have hoodd : Odd (orderOf o) :=
    (odd_card_oddCoreIn σ.C).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ho)
  have hoL₀ : o ∈ σ.L₀ := by
    rw [hII.L_eq] at hoL
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hF₀2
      ((inf_le_left.trans (σ.D_le_N hσ)).trans hσ.N_le_normalizer_L₀) hoL
    exact mem_of_pow_two_pow_mem_of_odd hoodd k hk
  have hoC : o ∈ σ.C := oddCoreIn_le σ.C ho
  have hoJO : o ∈ ((J ⊔ σ.ON : Subgroup G) : Set G) := hJ.sup_eq ▸ hoL₀
  rw [Subgroup.coe_mul_of_left_le_normalizer_right J σ.ON (hJN.trans σ.N_le_normalizer_ON)]
    at hoJO
  obtain ⟨j, hj, a, ha, hja⟩ := hoJO
  have hja : j * a = o := hja
  have hjT : ∀ t ∈ σ.T, j⁻¹ * t * j⁻¹⁻¹ * t⁻¹ ∈ M := by
    intro t ht
    have htN : t ∈ σ.N := σ.T_le_N hσ ht
    have heq : t * (j * a) = j * a * t := by
      rw [hja]
      exact Subgroup.mem_centralizer_iff.mp hoC t ht
    have h1 : j⁻¹ * t * j⁻¹⁻¹ * t⁻¹ = a * (t * a * t⁻¹)⁻¹ := by
      calc j⁻¹ * t * j⁻¹⁻¹ * t⁻¹ = j⁻¹ * (t * (j * a)) * a⁻¹ * t⁻¹ := by group
        _ = j⁻¹ * (j * a * t) * a⁻¹ * t⁻¹ := by rw [heq]
        _ = a * (t * a * t⁻¹)⁻¹ := by group
    have hJmem : j⁻¹ * t * j⁻¹⁻¹ * t⁻¹ ∈ J := by
      have : j⁻¹ * t * j⁻¹⁻¹ * t⁻¹ = j⁻¹ * (t * j * t⁻¹) := by group
      rw [this]
      exact J.mul_mem (J.inv_mem hj) ((Subgroup.mem_normalizer_iff.mp (hJ.normal htN) j).mp hj)
    have hOmem : j⁻¹ * t * j⁻¹⁻¹ * t⁻¹ ∈ σ.ON := by
      rw [h1]
      exact σ.ON.mul_mem ha (σ.ON.inv_mem
        ((Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_ON htN) a).mp ha))
    rw [hMdef, ← hJ.inf_eq]
    exact ⟨hJmem, hOmem⟩
  obtain ⟨m, hm, hmT⟩ := exists_inv_mul_mem_centralizer (σ.S.isPGroup'.to_le (σ.T_le_S hσ))
    hModd ((σ.T_le_N hσ).trans hNM) hjT
  have hhC : j * m ∈ σ.C := by
    have : j * m = (m⁻¹ * j⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hmT
  have hhJ : j * m ∈ J := J.mul_mem hj (hMJ hm)
  have ha' : m⁻¹ * a ∈ σ.C ⊓ σ.ON := by
    refine ⟨?_, σ.ON.mul_mem (σ.ON.inv_mem (hMO hm)) ha⟩
    have : m⁻¹ * a = (j * m)⁻¹ * o := by rw [← hja]; group
    rw [this]
    exact σ.C.mul_mem (σ.C.inv_mem hhC) hoC
  have hhO : j * m ∈ oddCoreIn σ.C := by
    have : j * m = o * (m⁻¹ * a)⁻¹ := by rw [← hja]; group
    rw [this]
    exact (oddCoreIn σ.C).mul_mem ho ((oddCoreIn σ.C).inv_mem (σ.C_inf_ON_le_oddCoreIn_C ha'))
  have hhWM : j * m ∈ ((W ⊔ M : Subgroup G) : Set G) := by
    have : j * m ∈ oddCoreIn σ.C ⊓ J ⊔ M := Subgroup.mem_sup_left ⟨hhO, hhJ⟩
    rw [← hW.2.2.2] at this
    exact this
  rw [Subgroup.coe_mul_of_left_le_normalizer_right W M ((hW.1.trans hJN).trans hNM)] at hhWM
  obtain ⟨w, hw, m', hm', hwm⟩ := hhWM
  have hwm : w * m' = j * m := hwm
  have hm'C : m' ∈ σ.C := by
    have : m' = w⁻¹ * (j * m) := by rw [← hwm]; group
    rw [this]
    exact σ.C.mul_mem (σ.C.inv_mem (oddCoreIn_le σ.C (hWO hw))) hhC
  have hx : m' * (m⁻¹ * a) ∈ σ.C ⊓ σ.ON :=
    (σ.C ⊓ σ.ON).mul_mem ⟨hm'C, hMO hm'⟩ ha'
  have hfx : f⁻¹ * (m' * (m⁻¹ * a)) * f ∈ σ.C ⊓ σ.ON := by
    have hfn : f⁻¹ ∈ Subgroup.normalizer ((σ.C ⊓ σ.ON : Subgroup G) : Set G) :=
      Subgroup.inv_mem _ (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨σ.D_le_normalizer_C hfD, σ.N_le_normalizer_ON hfN⟩)
    have := (Subgroup.mem_normalizer_iff.mp hfn _).mp hx
    simpa using this
  refine ⟨w * f, Subgroup.mul_mem_sup hw hfD, f⁻¹ * (m' * (m⁻¹ * a)) * f, hfx, ?_⟩
  change w * f * (f⁻¹ * (m' * (m⁻¹ * a)) * f) = c
  rw [← hof, ← hja]
  calc w * f * (f⁻¹ * (m' * (m⁻¹ * a)) * f) = (w * m') * m⁻¹ * a * f := by group
    _ = j * a * f := by rw [hwm]; group

theorem lemmaV31_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts) :
    ∀ J : Subgroup G, σ.IsV21Layer J → V56.LemmaV31 σ J := by
  intro J hJ
  obtain ⟨hne, hW⟩ := σ.lemmaV31 hσ hII hJ.le hJ.pCore_le hJ.sup_eq hJ.inf_eq hJ.normal
    hJ.commutator_le hJ.sl2 hN.oddCore_C_inf_L₀_cyclic hN.oddCore_C_inf_L₀_coprime
    hN.oddCore_C_inf_L₀_centralized hN.oddCore_C_inf_L₀_inverted
  exact ⟨hne, fun W hW' => (hW W hW').2.1,
    fun W hW' => σ.covers hσ hII hN hJ hW' (hW W hW').2.2.2.1⟩

theorem lemmaV33_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts) :
    ∀ J : Subgroup G, σ.IsV21Layer J → V56.LemmaV33 σ J := by
  intro J hJ
  refine ⟨fun W hW => ?_, fun W hW P hP => ?_, fun hr W hW d => ?_⟩
  · exact (σ.lemmaV33 hσ hII hJ.le hJ.pCore_le hJ.sup_eq hJ.inf_eq hJ.normal hJ.commutator_le
      hJ.sl2 hN.oddCore_C_inf_L₀_coprime hW).1
  · exact ((σ.lemmaV33 hσ hII hJ.le hJ.pCore_le hJ.sup_eq hJ.inf_eq hJ.normal hJ.commutator_le
      hJ.sl2 hN.oddCore_C_inf_L₀_coprime hW).2.2.1 P hP).symm
  · exact σ.lemmaV33v hσ hII hJ.le hJ.pCore_le hJ.sup_eq hJ.inf_eq hJ.normal hJ.commutator_le
      hJ.sl2 hN.oddCore_C_inf_L₀_coprime hN.oddCore_C_inf_L₀_centralized
      hN.oddCore_C_inf_L₀_inverted hr d hW

end Setting

namespace Setting

variable {G : Type} [Group G] [Finite G] (σ : Setting G)

theorem cStructure_of (_hσ : σ.IsValid) (hN : σ.IVNFacts) (hT : σ.TIFacts) :
    V56.CStructure σ :=
  ⟨σ.oddCoreIn_C_sup_eq hN, hT.F₀_omega⟩

end Setting

end CFSG.ABGTheoremB
