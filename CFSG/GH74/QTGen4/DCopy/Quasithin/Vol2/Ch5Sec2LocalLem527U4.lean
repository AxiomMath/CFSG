module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem527U4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem527

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

open U4Ext F1
open scoped Pointwise

theorem stmt5_2_7_U4_of_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hF : RankOneListedFacts.{0}) (hF11 : StmtF11_5_2_F4) (h524 : Stmt5_2_4_F4) (h526 : Stmt5_2_6_F4)
    (hbor : Stmt5_2_6_borel_F4) : Stmt5_2_7_U4_F4 := by
  intro G _ _ T M L V H B D L₂ n m hyp hn hext
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59

  have hLns : ¬ Group.IsSolvable ↥L :=
    not_isSolvable_of_perfect h.commutator_eq h.maximal.1.2.1.1
  have hL₂ns : ¬ Group.IsSolvable ↥L₂ := by
    obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, -, hL₂P⟩
    · exact not_isSolvable_of_perfect hK₁.2.1 hK₁.1
    · exact not_isSolvable_of_perfect hL₂P.2.1 hL₂P.1
  obtain ⟨-, hL₂K, hKG2, -, -, -, -, -⟩ := h526 G T M L V H B D L₂ n hyp
  obtain ⟨hG1, hG2, -⟩ := hyp.parabolics_eq_F4 h331 hR (hbor G T M L V H B D L₂ n hyp)
  have h111 := Hyp111R.of_hyp111 hF (hF11 G T M L V H B D L₂ n hyp)
  obtain ⟨-, -, ⟨hBS, -, -⟩, -⟩ := h524 G T M L V H B D L₂ n hyp
  subst hL₂K
  set S := sec52S M H with hSdef
  set K := oTwoUpper H with hKdef

  have hML : M ≤ Subgroup.normalizer (L : Set G) := h.normal
  have hDL : D ≤ L := hN.2.1.1.trans inf_le_left
  have hBM : B ≤ M := hN.1.1.trans inf_le_left
  have hSM : S ≤ M := (pCoreOf_le 2 _).trans inf_le_left
  have hSp : IsPGroup 2 ↥S := pCoreOf_isPGroup 2 (M ⊓ H)
  have hBodd : ∀ b ∈ B, Odd (orderOf b) := fun b hb =>
    Odd.of_dvd_nat hN.1.2.1 (Subgroup.orderOf_dvd_natCard B hb)
  have hDodd : ∀ d ∈ D, Odd (orderOf d) := fun d hd =>
    Odd.of_dvd_nat hN.2.1.2.1 (Subgroup.orderOf_dvd_natCard D hd)
  have hSL : S ⊓ L = T ⊓ L := h.inf_L_eq_F4 h331 hR hyp.hStar
  have hborL : borelOf L S = D ⊔ (S ⊓ L) := by
    have : borelOf L S = borelL T L := by
      unfold borelOf
      rw [hSL]
    rw [this, ← h.borelL_eq_sup hN.2.1, hSL]
  have hSpow : ∀ s ∈ S, ∃ k : ℕ, s ^ 2 ^ k = 1 := fun s hs => by
    obtain ⟨k, hk⟩ := hSp ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

  have hG1core : perfectCore (sec52G1 M L H B K) = L := by
    rw [hG1]
    have hQA := (F1.bigB_le_normalizer_left h111).1
    have hAn : (L.subgroupOf (L ⊔ bigB L K S)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hQA)
    exact le_antisymm
      (perfectCore_le_of_sup_solvable le_sup_left hAn rfl (F1.isSolvable_bigB h111))
      (le_perfectCore_of_perfect le_sup_left h.commutator_eq)
  have hG2core : perfectCore (sec52G2 M H D K) = K := hKG2.symm
  have hLG₁ : L ≤ sec52G1 M L H B K := le_sup_left.trans le_sup_left
  have hSG₁ : S ≤ sec52G1 M L H B K := le_sup_right.trans le_sup_left
  have hBKG₁ : B ⊓ K ≤ sec52G1 M L H B K := le_sup_right
  have hKG₂ : K ≤ sec52G2 M H D K := le_sup_right
  have hSG₂ : S ≤ sec52G2 M H D K := le_sup_right.trans le_sup_left
  have hDG₂ : D ≤ sec52G2 M H D K := le_sup_left.trans le_sup_left

  obtain ⟨Y₀, _, Yh, _, ι, hY₀, hι, hidx, Th, Mh₁, Mh₂, hpair, ⟨Φ⟩⟩ := hext
  obtain ⟨K', _, hK', ⟨e⟩⟩ := U4Par.exists_hypSU_equiv_of_lieModel hY₀
  have hfin : Finite Yh :=
    (U4Par.exists_embedding (Or.inr ⟨Y₀, inferInstance, ι, hY₀, hι, hidx⟩)).1
  have hψ₀ : Function.Injective (ι.comp e.toMonoidHom) := hι.comp e.injective
  have hidx₀ : (ι.comp e.toMonoidHom).range.index ≤ 2 := by
    rw [F431.U42.Am.range_comp_mulEquiv, hidx]
  obtain ⟨ψ, hψ, hrange, hU⟩ := U4V.exists_adapted hK' hψ₀ hidx₀ hpair.1
  rw [← hrange] at hidx₀ hU

  have hm : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 1 := by
      have := hK'.one_le
      omega
    subst hm1
    rcases U4V.exists_isSolvable_of_isYAmalgamPair
        (Or.inr ⟨Y₀, inferInstance, ι, hY₀, hι, hidx⟩) hpair with hs | hs
    · have h1 : Group.IsSolvable ↥(sec52G1 M L H B K) :=
        Group.isSolvable_of_surjective (f := (isoφ1 Φ).symm.toMonoidHom) (isoφ1 Φ).symm.surjective
      exact hLns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLG₁)
        (Subgroup.inclusion_injective hLG₁))
    · have h1 : Group.IsSolvable ↥(sec52G2 M H D K) :=
        Group.isSolvable_of_surjective (f := (isoφ2 Φ).symm.toMonoidHom) (isoφ2 Φ).symm.surjective
      exact hL₂ns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKG₂)
        (Subgroup.inclusion_injective hKG₂))

  have hpair' := U4V.isYAmalgamPair_swap hpair
  have s1a : ∀ g : ↥(sec52G1 M L H B K), (g : G) ∈ L → ((isoφ1 Φ g : ↥Mh₁) : Yh) ∈ ψ.range :=
    fun g hg => perfectCore_le_of_index_le_two hidx₀ Mh₁
      ((mem_perfectCore_iff_of_equiv (isoφ1 Φ) g).mp (by rw [hG1core]; exact hg))
  have s1b : ∀ g : ↥(sec52G1 M L H B K), ∀ k : ℕ, g ^ 2 ^ k = 1 →
      ((isoφ1 Φ g : ↥Mh₁) : Yh) ∈ ψ.range → (g : G) ∈ L := fun g k hk hgR => by
    have := mem_perfectCore_of_mem_range hm hK' ψ hψ hidx₀ hpair' hU (isoφ1 Φ) g hk hgR
    rwa [hG1core] at this
  have s2a : ∀ g : ↥(sec52G2 M H D K), (g : G) ∈ K → ((isoφ2 Φ g : ↥Mh₂) : Yh) ∈ ψ.range :=
    fun g hg => perfectCore_le_of_index_le_two hidx₀ Mh₂
      ((mem_perfectCore_iff_of_equiv (isoφ2 Φ) g).mp (by rw [hG2core]; exact hg))
  have s2b : ∀ g : ↥(sec52G2 M H D K), ∀ k : ℕ, g ^ 2 ^ k = 1 →
      ((isoφ2 Φ g : ↥Mh₂) : Yh) ∈ ψ.range → (g : G) ∈ K := fun g k hk hgR => by
    have := mem_perfectCore_of_mem_range hm hK' ψ hψ hidx₀ hpair hU (isoφ2 Φ) g hk hgR
    rwa [hG2core] at this
  have hcompat : ∀ x (h1 : x ∈ sec52G1 M L H B K) (h2 : x ∈ sec52G2 M H D K),
      ((isoφ1 Φ ⟨x, h1⟩ : ↥Mh₁) : Yh) = ((isoφ2 Φ ⟨x, h2⟩ : ↥Mh₂) : Yh) := fun x h1 h2 =>
    (coe_isoφ12_eq_φ1 Φ ⟨x, Subgroup.mem_inf.mpr ⟨h1, h2⟩⟩).symm.trans
      (coe_isoφ12_eq_φ2 Φ ⟨x, Subgroup.mem_inf.mpr ⟨h1, h2⟩⟩)

  have hSLK : S ⊓ L = S ⊓ K := by
    ext s
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hs, hsL⟩
      obtain ⟨k, hk⟩ := hSpow s hs
      refine ⟨hs, s2b ⟨s, hSG₂ hs⟩ k (Subtype.ext (by simpa using hk)) ?_⟩
      rw [← hcompat s (hSG₁ hs) (hSG₂ hs)]
      exact s1a ⟨s, hSG₁ hs⟩ hsL
    · rintro ⟨hs, hsK⟩
      obtain ⟨k, hk⟩ := hSpow s hs
      refine ⟨hs, s1b ⟨s, hSG₁ hs⟩ k (Subtype.ext (by simpa using hk)) ?_⟩
      rw [hcompat s (hSG₁ hs) (hSG₂ hs)]
      exact s2a ⟨s, hSG₂ hs⟩ hsK

  set G₁' := L ⊔ (S ⊓ L) ⊔ (B ⊓ K) with hG₁'
  set G₂' := D ⊔ (S ⊓ L) ⊔ K with hG₂'
  have hA₁ : G₁' ≤ sec52G1 M L H B K :=
    sup_le (sup_le hLG₁ (inf_le_left.trans hSG₁)) hBKG₁
  have hA₂ : G₂' ≤ sec52G2 M H D K :=
    sup_le (sup_le hDG₂ (inf_le_left.trans hSG₂)) hKG₂
  set N₁ : Subgroup G := (ψ.range.comap (Mh₁.subtype.comp (isoφ1 Φ).toMonoidHom)).map
    (sec52G1 M L H B K).subtype with hN₁def
  have hN₁ : ∀ g : ↥(sec52G1 M L H B K), (g : G) ∈ N₁ ↔ ((isoφ1 Φ g : ↥Mh₁) : Yh) ∈ ψ.range :=
    fun g => Subgroup.mem_map_iff_mem (sec52G1 M L H B K).subtype_injective
  set N₂ : Subgroup G := (ψ.range.comap (Mh₂.subtype.comp (isoφ2 Φ).toMonoidHom)).map
    (sec52G2 M H D K).subtype with hN₂def
  have hN₂ : ∀ g : ↥(sec52G2 M H D K), (g : G) ∈ N₂ ↔ ((isoφ2 Φ g : ↥Mh₂) : Yh) ∈ ψ.range :=
    fun g => Subgroup.mem_map_iff_mem (sec52G2 M H D K).subtype_injective
  have hLN₁ : L ≤ N₁ := fun y hy => (hN₁ ⟨y, hLG₁ hy⟩).mpr (s1a _ hy)
  have hBKN₁ : B ⊓ K ≤ N₁ := fun y hy => (hN₁ ⟨y, hBKG₁ hy⟩).mpr (mem_of_odd_orderOf hidx₀
    (by rw [orderOf_coe_equiv]; exact hBodd y hy.1))
  have hKN₂ : K ≤ N₂ := fun y hy => (hN₂ ⟨y, hKG₂ hy⟩).mpr (s2a _ hy)
  have hDN₂ : D ≤ N₂ := fun y hy => (hN₂ ⟨y, hDG₂ hy⟩).mpr (mem_of_odd_orderOf hidx₀
    (by rw [orderOf_coe_equiv]; exact hDodd y hy))
  have hG₁'N₁ : G₁' ≤ N₁ := sup_le (sup_le hLN₁ (inf_le_right.trans hLN₁)) hBKN₁
  have hG₂'N₂ : G₂' ≤ N₂ :=
    sup_le (sup_le hDN₂ (hSLK.le.trans (inf_le_right.trans hKN₂))) hKN₂
  have h₁ : ∀ x : ↥(sec52G1 M L H B K),
      (x : G) ∈ G₁' ↔ ((isoφ1 Φ x : ↥Mh₁) : Yh) ∈ Mh₁ ⊓ ψ.range := by
    intro x
    constructor
    · intro hx
      exact ⟨(isoφ1 Φ x).2, (hN₁ x).mp (hG₁'N₁ hx)⟩
    · intro hx
      have hxN : (x : G) ∈ N₁ := (hN₁ x).mpr hx.2
      have hx' : (x : G) ∈ L ⊔ (S ⊔ (B ⊓ K)) := by
        rw [← sup_assoc]
        exact x.2
      have hnL : S ⊔ (B ⊓ K) ≤ Subgroup.normalizer (L : Set G) :=
        sup_le (hSM.trans hML) (inf_le_left.trans (hBM.trans hML))
      obtain ⟨l, hl, y, hy, hxy⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hnL).mp hx'
      obtain ⟨s, hs, b, hb, hyb⟩ :=
        (F1.mem_sup_iff_exists_mul_of_normalizes (inf_le_left.trans hBS)).mp hy
      have hsN : s ∈ N₁ := by
        have e : s = l⁻¹ * x * b⁻¹ := by
          rw [hxy, hyb]
          group
        rw [e]
        exact N₁.mul_mem (N₁.mul_mem (N₁.inv_mem (hLN₁ hl)) hxN) (N₁.inv_mem (hBKN₁ hb))
      obtain ⟨k, hk⟩ := hSpow s hs
      have hsL : s ∈ L :=
        s1b ⟨s, hSG₁ hs⟩ k (Subtype.ext (by simpa using hk)) ((hN₁ ⟨s, hSG₁ hs⟩).mp hsN)
      rw [hxy, hyb]
      exact G₁'.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hl))
        (G₁'.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨hs, hsL⟩))
          (Subgroup.mem_sup_right hb))
  have h₂ : ∀ x : ↥(sec52G2 M H D K),
      (x : G) ∈ G₂' ↔ ((isoφ2 Φ x : ↥Mh₂) : Yh) ∈ Mh₂ ⊓ ψ.range := by
    intro x
    constructor
    · intro hx
      exact ⟨(isoφ2 Φ x).2, (hN₂ x).mp (hG₂'N₂ hx)⟩
    · intro hx
      have hxN : (x : G) ∈ N₂ := (hN₂ x).mpr hx.2
      have hx' : (x : G) ∈ K ⊔ bigB L K S := by
        rw [← hG2]
        exact x.2
      obtain ⟨k₀, hk₀, y, hy, hxy⟩ :=
        (F1.mem_sup_iff_exists_mul_of_normalizes (F1.bigB_le_normalizer_left h111).2).mp hx'
      have hy' : y ∈ (borelOf L S : Set G) * (borelOf K S : Set G) * (S : Set G) := by
        rw [← F1.coe_bigB h111]
        exact hy
      obtain ⟨a, ⟨b₁, hb₁, b₂, hb₂, rfl⟩, s, hs, rfl⟩ := hy'
      have hb₁' : b₁ ∈ G₂' := by
        have h1 : b₁ ∈ D ⊔ (S ⊓ L) := by
          rw [← hborL]
          exact hb₁
        exact (sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) :
          D ⊔ (S ⊓ L) ≤ G₂') h1
      have hb₂K : b₂ ∈ K := borelOf_le K S hb₂
      have hsN : s ∈ N₂ := by
        have e : s = (k₀ * (b₁ * b₂))⁻¹ * x := by
          rw [hxy]
          group
        rw [e]
        exact N₂.mul_mem (N₂.inv_mem (N₂.mul_mem (hKN₂ hk₀)
          (N₂.mul_mem (hG₂'N₂ hb₁') (hKN₂ hb₂K)))) hxN
      obtain ⟨k, hk⟩ := hSpow s hs
      have hsK : s ∈ K :=
        s2b ⟨s, hSG₂ hs⟩ k (Subtype.ext (by simpa using hk)) ((hN₂ ⟨s, hSG₂ hs⟩).mp hsN)
      have hsG : s ∈ G₂' := by
        have h1 : s ∈ S ⊓ L := by
          rw [hSLK]
          exact ⟨hs, hsK⟩
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_right h1)
      rw [hxy]
      exact G₂'.mul_mem (Subgroup.mem_sup_right hk₀)
        (G₂'.mul_mem (G₂'.mul_mem hb₁' (Subgroup.mem_sup_right hb₂K)) hsG)

  obtain ⟨i₂, hM₂N, hM₂R⟩ := U4V.inf_eq_of_adapted hK' ψ hψ hidx₀ hpair hU
  obtain ⟨i₁, hM₁N, hM₁R⟩ := U4V.inf_eq_of_adapted hK' ψ hψ hidx₀ hpair' hU
  have hne : i₁ ≠ i₂ := by
    rintro rfl
    exact hpair.2.1 (hM₁N.trans hM₂N.symm)
  set P : Fin 2 → Subgroup (hypSU hK' 2 0) := ![U4Par.parP hK', U4Par.parP2 hK'] with hP
  have hMP : ∀ (M' : Subgroup Yh) (i : Fin 2),
      M' ⊓ ψ.range = (![(U4Par.parP hK').map ψ, (U4Par.parP2 hK').map ψ] : Fin 2 → Subgroup Yh) i →
      M' ⊓ ψ.range = (P i).map ψ := by
    intro M' i hi
    rw [hi]
    fin_cases i <;> rfl
  have hpairP : IsYAmalgamPair (hypUnitriangular hK' 2 0) (P i₁) (P i₂) := by
    fin_cases i₁ <;> fin_cases i₂
    · exact absurd rfl hne
    · exact U4Par.isYAmalgamPair_parP_parP2 hK'
    · exact U4V.isYAmalgamPair_swap (U4Par.isYAmalgamPair_parP_parP2 hK')
    · exact absurd rfl hne
  have Ψ : (RankTwoAmalgam.ofSubgroups G₁' G₂').Iso
      (RankTwoAmalgam.ofSubgroups (P i₁) (P i₂)) :=
    F431.U42.Am.isoTrans (ofSubgroupsIsoRestrict Φ hA₁ hA₂ inf_le_left inf_le_left h₁ h₂)
      (F431.U42.Am.isoTrans
        (F431.U42.Am.ofSubgroupsCongr (hMP Mh₁ i₁ hM₁R) (hMP Mh₂ i₂ hM₂R))
        (F431.U42.Am.isoSymm (F431.U42.Am.ofSubgroupsMapInj ψ hψ (P i₁) (P i₂))))
  refine ⟨by omega, hSLK, ?_⟩
  exact ⟨hypSU hK' 2 0, inferInstance, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hY₀,
    hypUnitriangular hK' 2 0, P i₁, P i₂, hpairP, ⟨Ψ⟩⟩

end CFSG.Quasithin.H13
