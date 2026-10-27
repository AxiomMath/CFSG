module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6D8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31Phi

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

section Config

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s x z₁ z₂ : G} {K : Subgroup G}

theorem A3A3K.rK_eq (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hK : A3A3K T M H S L s x z₁ z₂ K) (e₀ : ↥K ≃* alternatingGroup (Fin 6)) :
    baum S ⊓ K = blockU L ⊔ conjR (blockU L) x ∧ Nat.card ↥(baum S ⊓ K) = 8 := by
  have hcs := hK.cs
  have hA := hK.isA4
  have hB := basic31 hD h27_1 hK.toA3A3
  have hxN : x ∈ normalizer (baum S : Set G) := hK.toA3A3x.x_mem_normalizer_baum hB
  have hxG : x ∈ centralizerElem z₂ := Subgroup.mem_centralizer_singleton_iff.mpr hK.x_comm₂
  have hxK : x ∈ normalizer (K : Set G) := hK.K_norm hxG
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hK.a3
  have hUK : blockU L ≤ K := hA.le.trans hK.L_le_K
  have hUxB : conjR (blockU L) x ≤ baum S :=
    (C5.conjSubgroup_mono hUB x).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))
  have hUxK : conjR (blockU L) x ≤ K :=
    (C5.conjSubgroup_mono hUK x).trans (le_of_eq (C5.conjSubgroup_eq_self hxK))
  have hJR : blockU L ⊔ conjR (blockU L) x ≤ baum S ⊓ K :=
    sup_le (le_inf hUB hUK) (le_inf hUxB hUxK)
  have hT2 : IsPGroup 2 ↥T := hcs.setting.sylow.isPGroup
  have hRT : baum S ⊓ K ≤ T :=
    inf_le_left.trans (inf_le_left.trans hcs.le_T)
  have hR2 : IsPGroup 2 ↥(baum S ⊓ K) := hT2.to_le hRT
  have hcardK : Nat.card ↥K = 360 := (Nat.card_congr e₀.toEquiv).trans card_alt6'
  have hdvd : Nat.card ↥(baum S ⊓ K) ∣ 8 := by
    obtain ⟨n, hn⟩ := hR2.exists_card_eq
    have h1 : Nat.card ↥(baum S ⊓ K) ∣ 360 :=
      hcardK ▸ Subgroup.card_dvd_of_le (inf_le_right : baum S ⊓ K ≤ K)
    have hn3 : n ≤ 3 := by
      by_contra hcon
      have h4 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      rw [hn] at h1
      have := h4.trans h1
      norm_num at this
    rw [hn]
    exact (pow_dvd_pow 2 hn3 : 2 ^ n ∣ 2 ^ 3)
  have hne : ¬ conjR (blockU L) x ≤ blockU L := fun h =>
    hK.x_good (fun y hy => Subgroup.mem_centralizer_iff.mpr fun v hv =>
      hA.comm_U v hv y (h hy))
  have hJcard : Nat.card ↥(blockU L ⊔ conjR (blockU L) x) = 8 := by
    have hJdvd : Nat.card ↥(blockU L ⊔ conjR (blockU L) x) ∣ 8 :=
      (Subgroup.card_dvd_of_le hJR).trans hdvd
    have hge : 4 ≤ Nat.card ↥(blockU L ⊔ conjR (blockU L) x) := by
      rw [← hA.card_U]
      exact Subgroup.card_le_of_le le_sup_left
    have hne4 : Nat.card ↥(blockU L ⊔ conjR (blockU L) x) ≠ 4 := by
      intro h4
      have : blockU L ⊔ conjR (blockU L) x ≤ blockU L :=
        (Subgroup.eq_of_le_of_card_ge (le_sup_left : blockU L ≤ blockU L ⊔ conjR (blockU L) x)
          (by rw [h4, hA.card_U])).symm.le
      exact hne (le_sup_right.trans this)
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (by simpa using hJdvd :
      Nat.card ↥(blockU L ⊔ conjR (blockU L) x) ∣ 2 ^ 3)
    rw [hi'] at hge hne4 ⊢
    interval_cases i <;> simp_all
  have hReq : baum S ⊓ K = blockU L ⊔ conjR (blockU L) x :=
    (Subgroup.eq_of_le_of_card_ge hJR
      (by rw [hJcard]; exact Nat.le_of_dvd (by norm_num) hdvd)).symm
  exact ⟨hReq, by rw [hReq]; exact hJcard⟩

theorem A3A3K.rK_dihedral (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hK : A3A3K T M H S L s x z₁ z₂ K)
    (e₀ : ↥K ≃* alternatingGroup (Fin 6)) :
    Nonempty (↥(baum S ⊓ K) ≃* DihedralGroup 4) := by
  obtain ⟨-, hcard⟩ := hK.rK_eq hD h27_1 e₀
  let D : Subgroup (alternatingGroup (Fin 6)) := ((baum S ⊓ K).subgroupOf K).map e₀.toMonoidHom
  have hD8 : Nat.card ↥D = 8 := by
    have h1 : Nat.card ↥D = Nat.card ↥((baum S ⊓ K).subgroupOf K) :=
      Subgroup.card_map_of_injective e₀.injective
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : baum S ⊓ K ≤ K)).toEquiv]
    exact hcard
  obtain ⟨e⟩ := nonempty_dihedral_of_card_eight D hD8
  exact ⟨((Subgroup.subgroupOfEquivOfLe (inf_le_right : baum S ⊓ K ≤ K)).symm.trans
    (Subgroup.equivMapOfInjective _ e₀.toMonoidHom e₀.injective)).trans e⟩

theorem A3A3K.u_comm_rK (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hK : A3A3K T M H S L s x z₁ z₂ K)
    (e₀ : ↥K ≃* alternatingGroup (Fin 6)) :
    ∀ u ∈ blockU2 L s, ∀ r ∈ baum S ⊓ K, u * r = r * u := by
  obtain ⟨hReq, -⟩ := hK.rK_eq hD h27_1 e₀
  have hA := hK.isA4
  have hAs := hK.isA4s
  have hcross := (hK.toA3A3x.cross_comm hD h27_1).2
  intro u hu r hr
  rw [hReq] at hr
  have hle : blockU L ⊔ conjR (blockU L) x ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr ?_)
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    · exact hK.comm_elem v (hA.le hv) u (hAs.le hu)
    · exact (hcross u hu v hv).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hr)).symm

end Config

end CFSG.QuasithinUnique.DoubleA3
