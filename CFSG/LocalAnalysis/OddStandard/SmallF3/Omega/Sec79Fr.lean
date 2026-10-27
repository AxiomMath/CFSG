module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79Y
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79Norm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Tab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec79_frattini [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {x : G} (hx : x ∈ S ⊓ centralizer (B : Set G))
    (hx2 : x * x = t) : MSub S B ≤ centralizer ({t} : Set G) := by
  intro m hm
  classical
  let Y : Subgroup G := S ⊓ centralizer (B : Set G)
  let f : G →* G := (MulAut.conj m).toMonoidHom
  have hY : IsSylow2Of Y (centralizer (ASub S B : Set G)) :=
    sec79_Y_sylow h36 h76 hP h78 hc
  have hf : Function.Injective f := fun _ _ h => (MulAut.conj m).injective h
  have hKC : Y.map f ≤ centralizer (ASub S B : Set G) := by
    rintro k ⟨y, hy, rfl⟩
    change (MulAut.conj m) y ∈ centralizer (ASub S B : Set G)
    rw [MulAut.conj_apply]
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have hyC : y ∈ centralizer (ASub S B : Set G) := hY.1 hy
    have ha' : m⁻¹ * a * m ∈ ASub S B :=
      (Subgroup.mem_normalizer_iff''.mp hm a).mp ha
    have hcomm := (Subgroup.mem_centralizer_iff.mp hyC) (m⁻¹ * a * m) ha'
    calc a * (m * y * m⁻¹) = m * ((m⁻¹ * a * m) * y) * m⁻¹ := by group
      _ = m * (y * (m⁻¹ * a * m)) * m⁻¹ := by rw [hcomm]
      _ = (m * y * m⁻¹) * a := by group
  have hK : IsPGroup 2 (Y.map f) :=
    hY.2.1.of_equiv (Subgroup.equivMapOfInjective Y f hf)
  obtain ⟨c, hcC, hconj⟩ := exists_conj_le_of_isSylow2Of hY hK hKC
  have hxY : x ∈ Y := hx
  have hk : m * x * m⁻¹ ∈ Y.map f := by
    refine Subgroup.mem_map.mpr ⟨x, hxY, ?_⟩
    change (MulAut.conj m) x = m * x * m⁻¹
    rw [MulAut.conj_apply]
  have hu : c * (m * x * m⁻¹) * c⁻¹ ∈ Y := hconj _ hk
  have hu_eq : c * (m * x * m⁻¹) * c⁻¹ = (c * m) * x * (c * m)⁻¹ := by group
  have hu2 : (c * (m * x * m⁻¹) * c⁻¹) * (c * (m * x * m⁻¹) * c⁻¹) =
      (c * m) * t * (c * m)⁻¹ := by
    rw [hu_eq,
      show ((c * m) * x * (c * m)⁻¹) * ((c * m) * x * (c * m)⁻¹) =
        (c * m) * (x * x) * (c * m)⁻¹ by group,
      hx2]
  have hu_sq := sec79_sq_in h36 h76 hP h78 hc hu
  have hX : (c * m) * t * (c * m)⁻¹ = t := by
    rcases hu_sq with h1 | ht
    · exfalso
      have h1' : (c * m) * t * (c * m)⁻¹ = 1 := hu2.symm.trans h1
      have ht1 : t = 1 := by
        calc t = (c * m)⁻¹ * ((c * m) * t * (c * m)⁻¹) * (c * m) := by group
          _ = 1 := by rw [h1']; group
      have hinv := hc.ctx.involution
      rw [ht1, orderOf_one] at hinv
      exact absurd hinv (by norm_num)
    · exact hu2.symm.trans ht
  have htA : t ∈ ASub S B := by
    rw [h78 G t L S z g B hc]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hc_t : c ∈ centralizer ({t} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htA) hcC
  have hcm : c * m ∈ centralizer ({t} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h : (c * m) * t = t * (c * m) := by
      simpa [mul_assoc] using congrArg (fun x => x * (c * m)) hX
    exact h
  have hm' : m ∈ centralizer ({t} : Set G) := by
    have h := (centralizer ({t} : Set G)).mul_mem
      ((centralizer ({t} : Set G)).inv_mem hc_t) hcm
    rwa [show c⁻¹ * (c * m) = m by group] at h
  exact hm'

theorem sec79_no_alt2 [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    S ⊓ centralizer (B : Set G) ≤ ASub S B := by
  intro x hx
  by_contra hxA
  have hx2 : x * x = t := sec79_Y_sq h36 h76 hP h78 hc hx hxA
  have hM := sec79_frattini h36 h76 hP h78 hc hx hx2
  obtain ⟨n, hn, hnt⟩ := h77b G t L S z g B hc
  have hnC : n * t = t * n := Subgroup.mem_centralizer_singleton_iff.mp (hM hn.2)
  exact hnt hnC.symm

theorem sec79_no_i1_of_mem_A [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) {y : G}
    (hy : y ∈ zpowers t ⊔ B) (hyC : y ∉ centralizer (L : Set G)) :
    ¬ ∃ α : ℤˣ, InducesTypeSome L y 6 1 1 α := by
  rintro ⟨α, hα⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hctx := hc.ctx
  have hB_S : B ≤ S := hc.normalE16.1.trans inf_le_left
  have hB_L : B ≤ L := hc.normalE16.1.trans inf_le_right
  have hyS : y ∈ S := (sup_le (Subgroup.zpowers_le.mpr hctx.t_mem_S) hB_S) hy
  have hyCt : y ∈ centralizer ({t} : Set G) := hctx.sylow.1 hyS
  have hyN : y ∈ normalizer (L : Set G) := hctx.cent_le_normalizer h36 y hyCt
  have hyy : y * y = 1 := sec79_sq_one_of_mem_A hc hy
  have hy1 : y ≠ 1 := by
    intro h1
    exact hyC (by rw [h1]; exact Subgroup.one_mem _)
  have hy2 : orderOf y = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hyy) hy1
  have hinner : InnerOn L y := by
    change y ∈ L ⊔ centralizer (L : Set G)
    have hzt : zpowers t ≤ centralizer (L : Set G) :=
      Subgroup.zpowers_le.mpr hctx.t_mem_centralizer
    have hmem : y ∈ centralizer (L : Set G) ⊔ L := (sup_le_sup hzt hB_L) hy
    rwa [sup_comm] at hmem
  exact sec79_not_inner_of_i1 hP hctx.isOm6P hy2 hyN ⟨α, hα⟩ hinner

theorem asc82Lemma79a_of (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (h76 : Asc82Lemma76)
    (hP : Asc82Tab6P) (hP7 : Asc82Tab7P) (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) :
    Asc82Lemma79a := by
  intro G _ _ t L S z g B hc
  have hctx := hc.ctx
  refine hP7.hyp62_of_sylow G L hctx.isOm6P (centralizer ({t} : Set G)) S
    hctx.le_centralizer ?_ hctx.sylow (sec7_normalizer_decomp h72 hctx) B hc.normalE16 ?_
  · intro c hc'
    exact hctx.cent_le_normalizer h36 c hc'
  · intro y hyS hyC hyB
    have hyY : y ∈ S ⊓ centralizer (B : Set G) :=
      ⟨hyS, Subgroup.mem_centralizer_iff.mpr fun b hb => (hyB b hb).symm⟩
    have hyA : y ∈ ASub S B := sec79_no_alt2 h36 h76 hP h77b h78 hc hyY
    rw [h78 G t L S z g B hc] at hyA
    exact sec79_no_i1_of_mem_A h36 hP hc hyA hyC

end CFSG.OddStandard.SmallF3.Omega
