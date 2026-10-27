module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input1919

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input1919b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
  CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf innerAut)

@[expose] def NotBalanced119 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), CFSG.Open.IsQuasisimple X → GLAPPrimeCore p X = ⊥ →
    ((p = 5 ∧ IsSporType .Fi22 (X ⧸ Subgroup.center X)) ∨
      (p = 3 ∧ (IsLThreeFour (X ⧸ Subgroup.center X) ∨ IsAltType 5 (X ⧸ Subgroup.center X)))) →
    ¬ IsLocallyOTwoBalancedWrtP p 1 X

theorem notBalanced119_of_spor
    (hSpor : Input1919.Input19_19Spor) : NotBalanced119 := by
  intro X _ _ p hq hO h
  rcases h with ⟨rfl, hFi⟩ | ⟨rfl, hL | hA⟩
  · exact (hSpor X hq).1 hFi
  · exact Input1919.not_balanced_L34_core hq hO hL
  · exact Input1919.not_balanced_alt_core hq Nat.prime_three (by norm_num) hO
      ⟨5, le_rfl, hA, Or.inl (by norm_num)⟩

section L119

variable {G : Type} [Group G] [Finite G]

theorem layer_le119 {p : ℕ} (hp : p.Prime) {m : ℕ} {B M E A : Subgroup G} {a : G}
    (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1)
    (hNB : NotBalanced119) (hnot : Input_not_LTwoTwentySeven) (h115 : Prop115Statement)
    {b : G} (hbA0 : b ∈ E ⊓ A) (hb1 : b ≠ 1) (hbC : b ∈ Cg a)
    (hbp : IsPGroup p (Subgroup.zpowers b))
    {L : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))} (hL : IsSubnormal L ⊤)
    {Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))}
    (hQ : GLAPComponent p (L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨b, hbC⟩} :
        Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q)
    {X : Type} [Group X] [Finite X]
    (hQK : Nonempty ((↥Q ⧸ GLAPPrimeCore p ↥Q) ⧸ Subgroup.center (↥Q ⧸ GLAPPrimeCore p ↥Q) ≃*
      X ⧸ Subgroup.center X))
    (hTK : (p = 5 ∧ IsSporType .Fi22 (X ⧸ Subgroup.center X)) ∨
      (p = 3 ∧ IsLThreeFour (X ⧸ Subgroup.center X))) :
    Q ≤ barX p (Cg a) M := by
  obtain ⟨P, hP, hPQ, ⟨e⟩⟩ := l119_layer_piece hp hbC hbp hL hQ
  have hPq : CFSG.Open.IsQuasisimple (↥P ⧸ GLAPPrimeCore p ↥P) := l119_isQuasisimple_barOf hp hP
  obtain ⟨eK⟩ := hQK
  have eP : ((↥P ⧸ GLAPPrimeCore p ↥P) ⧸ Subgroup.center (↥P ⧸ GLAPPrimeCore p ↥P)) ≃*
      X ⧸ Subgroup.center X := e.symm.trans eK
  have hTP : (p = 5 ∧ IsSporType .Fi22
        ((↥P ⧸ GLAPPrimeCore p ↥P) ⧸ Subgroup.center (↥P ⧸ GLAPPrimeCore p ↥P))) ∨
      (p = 3 ∧ IsLThreeFour
        ((↥P ⧸ GLAPPrimeCore p ↥P) ⧸ Subgroup.center (↥P ⧸ GLAPPrimeCore p ↥P))) := by
    rcases hTK with ⟨h5, h⟩ | ⟨h3, h⟩
    · exact Or.inl ⟨h5, l119_isSporType_congr _ eP.symm h⟩
    · exact Or.inr ⟨h3, l119_isLThreeFour_congr eP.symm h⟩
  have h1 : ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p P) :=
    hNB _ p hPq (glaPPrimeCore_quotient_eq_bot hp) (by
      rcases hTP with ⟨h5, h⟩ | ⟨h3, h⟩
      · exact Or.inl ⟨h5, h⟩
      · exact Or.inr ⟨h3, Or.inl h⟩)
  have h2 : p = 3 → IsLTwoTwentySeven (barOf p P) → ¬ IsCompLocallyOTwoBalanced p 1 A P := by
    intro hp3 hL27 _
    rcases hTP with ⟨h5, -⟩ | ⟨-, h3⟩
    · omega
    · exact hnot (barOf p P) hL27 (Or.inl h3)
  have hJ : GLAPComponent p (Cg2 b a) P := by
    unfold Cg2
    rw [l119_cg2_eq]
    exact hP
  rcases h115 hSec ha ha1 hbA0 hb1 hJ h1 h2 with hPM | ⟨A1, hA1, haA1⟩
  · rw [← hPQ]
    exact CFSG.LocalAnalysis.GLTheoremB.barX_mono p hPM
  · exact absurd ⟨A1, hA1, haA1⟩ hnotD

theorem no_bad119 {p : ℕ} {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (hp : p.Prime) (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hK : GLAPComponent p (Cg a) K) (hKM : ¬ K ≤ M)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1)
    (hK18 : (p = 5 ∧ IsSporType .Fi22 (barOf p K)) ∨
      (p = 3 ∧ IsLThreeFour (barOf p K ⧸ Subgroup.center (barOf p K))))
    (h111 : Prop111Statement) (hI22 : Input22_3_2) (hI18 : Input18_3_diag) (hNB : NotBalanced119)
    (hord : Input_order_dvd) (hcent : Input_Fi22_centreless) (hnot : Input_not_LTwoTwentySeven)
    (h115 : Prop115Statement) :
    ¬ ∃ z : ↥(Cg a), (z : G) ∈ E ⊓ A ∧ (z : G) ≠ 1 ∧
      ((z : G) ∉ Subgroup.normalizer (K : Set G) ∨
        ∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨z₀, hz₀A, hz₀1, hbad⟩
  obtain ⟨hDDp, -⟩ := hSec.pair
  obtain ⟨-, hDp, hrA0⟩ := hDDp
  obtain ⟨hSCs, -⟩ := hDp
  obtain ⟨hSCp, -⟩ := hSCs
  obtain ⟨-, hAel, -⟩ := hSCp
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx => hAel.2 x hx
  have hACg : A ≤ Cg a := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hAcomm a ha x hx
  set A0 : Subgroup G := E ⊓ A with hA0
  have hA0A : A0 ≤ A := inf_le_right
  have hA0C : A0 ≤ Cg a := hA0A.trans hACg
  have hA0el : IsElemAbelian p A0 := l119_isElemAbelian_of_le hA0A hAel
  have hrA0 : 2 ≤ CFSG.Open.pRank p A0 := hrA0
  set A0C : Subgroup ↥(Cg a) := A0.subgroupOf (Cg a) with hA0Cdef
  set Bbar : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) :=
    A0C.map (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a))) with hBbar
  set Kb : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := barX p (Cg a) K with hKb
  set 𝓛 := Prop1116.fam p (Cg a) K A0C with h𝓛def
  set Yb : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := sSup 𝓛 with hYb
  have hKbc : IsComponentOf Kb ⊤ := l119_isComponent_barX hK
  have hKbmem : Kb ∈ 𝓛 := Prop1116.fam_base p (Cg a) K A0C
  have h𝓛c : ∀ X ∈ 𝓛, IsComponentOf X ⊤ := Prop1116.fam_comp hK A0C
  have hcomm𝓛 : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x := by
    rintro X ⟨w, -, rfl⟩ X' ⟨w', -, rfl⟩ hne x hx y hy
    exact l119_conj_comm hK hne hx hy
  have hYsub : IsSubnormal Yb ⊤ := l119_isSubnormal_sSup_components h𝓛c
  have hYcomp : ∀ X ∈ 𝓛, IsComponentOf X Yb := fun X hX => l119_isComponentOf_sSup h𝓛c hcomm𝓛 hX
  have hBcomm : ∀ z ∈ A0C, ∀ w ∈ A0C,
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w =
        QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z := by
    intro z hz w hw
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hAcomm _ (hA0A ((Subgroup.mem_subgroupOf).1 hz)) _ (hA0A ((Subgroup.mem_subgroupOf).1 hw))
  have hBnorm : Bbar ≤ Subgroup.normalizer ((Yb : Subgroup _) : Set _) := by
    rintro _ ⟨z, hz, rfl⟩
    exact Prop1116.fam_bar_normalizes A0C hz
  have hA0Cel : IsElemAbelian p A0C := l119_isElemAbelian_subgroupOf hA0el (Cg a)
  have hBel : IsElemAbelian p Bbar :=
    CFSG.SectionRank.isElemAbelian_map hA0Cel _
  have hB_rank : 2 ≤ CFSG.Open.pRank p Bbar := le_trans hrA0 (l119_pRank_image_ge hp hA0C hA0el)
  have hKbe : (↥K ⧸ GLAPPrimeCore p ↥K) ≃* ↥Kb := quotEquivBarX hp hK.1 hK.2.1
  have hKbT : (p = 5 ∧ IsSporType .Fi22 ↥Kb) ∨ (p = 3 ∧ IsLThreeFour (↥Kb ⧸ Subgroup.center ↥Kb)) := by
    rcases hK18 with ⟨h5, h⟩ | ⟨h3, h⟩
    · exact Or.inl ⟨h5, l119_isSporType_congr _ hKbe h⟩
    · exact Or.inr ⟨h3, l119_isLThreeFour_congr (l119_centerQuot_equiv hKbe) h⟩
  have hKbT' : (p = 5 ∧ IsSporType .Fi22 (↥Kb ⧸ Subgroup.center ↥Kb)) ∨
      (p = 3 ∧ IsLThreeFour (↥Kb ⧸ Subgroup.center ↥Kb)) := by
    rcases hKbT with ⟨h5, h⟩ | ⟨h3, h⟩
    · exact Or.inl ⟨h5, l119_isSporType_congr _ (l119_center_bot_quot (hcent _ h)).symm h⟩
    · exact Or.inr ⟨h3, h⟩
  have hpY : p ∣ Nat.card ↥Yb :=
    dvd_trans (hord ↥Kb p hp hKbT) (Subgroup.card_dvd_of_le (le_sSup hKbmem))
  have htrans : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, ∃ b ∈ Bbar, GLBConj b X = X' := by
    rintro X ⟨w, hw, rfl⟩ X' ⟨w', hw', rfl⟩
    exact ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) (w⁻¹ * w'),
      Subgroup.mem_map_of_mem _ (A0C.mul_mem (A0C.inv_mem hw) hw'), l119_conj_trans w w'⟩
  have hz₀C : z₀ ∈ A0C := Subgroup.mem_subgroupOf.2 hz₀A
  have hb₀B : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∈ Bbar :=
    Subgroup.mem_map_of_mem _ hz₀C
  have hz₀pow : z₀ ^ p = 1 := by
    apply Subtype.ext
    simpa using hApow _ hz₀A.2
  have hb₀1 : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ≠ 1 := by
    intro h
    apply hz₀1
    have h2 := l119_eq_one_of_pow_of_mem_core hp hz₀pow ((QuotientGroup.eq_one_iff _).1 h)
    simpa using congrArg Subtype.val h2
  have hJb₀ : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∈ Subgroup.centralizer (Yb : Set _) ∨
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∉ Subgroup.normalizer (Kb : Set _) := by
    rcases hbad with hN | hC
    · right
      intro hb
      exact hN (l119_mem_normalizer_of_bar hp hK z₀ hb)
    · left
      have hYc : Yb ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀} : Set _) := by
        refine sSup_le fun X hX => ?_
        obtain ⟨w, hw, rfl⟩ := hX
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact l119_centralizes_gLBConj (hBcomm z₀ hz₀C w hw) hC x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h2 := hYc hh
      rw [Subgroup.mem_centralizer_iff] at h2
      exact (h2 _ (Set.mem_singleton _)).symm
  have hLayer : ∀ b ∈ Bbar, b ≠ 1 → (b ∈ Subgroup.centralizer (Yb : Set _) ∨
      b ∉ Subgroup.normalizer (Kb : Set _)) →
      GLAPLayer p (Yb ⊓ Subgroup.centralizer ({b} : Set _)) ≤ barX p (Cg a) M := by
    intro b hb hb1 hJ
    have hbB := hb
    obtain ⟨z, hz, rfl⟩ := hb
    have hzA : (z : G) ∈ A0 := Subgroup.mem_subgroupOf.1 hz
    have hz1 : (z : G) ≠ 1 := by
      intro h
      apply hb1
      have hzeq : z = 1 := Subtype.ext h
      rw [hzeq, map_one]
    have hzpow : (z : G) ^ p = 1 := hApow _ hzA.2
    have hzC : (z : G) ∈ Cg a := z.2
    have hzp : IsPGroup p (Subgroup.zpowers (z : G)) := l119_isPGroup_zpowers hzpow
    have hzpow' : z ^ p = 1 := by
      apply Subtype.ext
      simpa using hzpow
    have hbord : orderOf (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) = p := by
      apply orderOf_eq_prime
      · rw [← map_pow, hzpow', map_one]
      · exact hb1
    have hdich : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z ∈ Subgroup.centralizer (Yb : Set _) ∨
        ∀ X ∈ 𝓛, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z ∉ Subgroup.normalizer (X : Set _) := by
      rcases hJ with hC | hN
      · left
        exact hC
      · right
        rintro X ⟨w, hw, rfl⟩ hmem
        apply hN
        exact (l119_normalizer_gLBConj_iff (hBcomm z hz w hw) Kb).1 hmem
    unfold GLAPLayer
    refine sSup_le fun Q hQ => ?_
    obtain ⟨X₀, hX₀, ⟨e0⟩⟩ := hI18 (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) p hp Yb 𝓛
      (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) hbord (hBnorm hbB) rfl hYcomp hcomm𝓛 hdich Q hQ
    obtain ⟨w, hw, rfl⟩ := hX₀
    have eK : ↥(GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w) Kb) ≃* ↥Kb :=
      (l119_gLBConj_equiv _ Kb).symm
    have hQK : Nonempty ((↥Q ⧸ GLAPPrimeCore p ↥Q) ⧸ Subgroup.center (↥Q ⧸ GLAPPrimeCore p ↥Q) ≃*
        ↥Kb ⧸ Subgroup.center ↥Kb) := ⟨e0.trans (l119_centerQuot_equiv eK)⟩
    exact layer_le119 hp hSec ha ha1 hnotD hNB hnot h115 hzA hz1 hzC hzp hYsub hQ hQK hKbT'
  have hYM : Yb ≤ barX p (Cg a) M := by
    have hI22' := hI22 (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) p hp Bbar Yb Kb 𝓛 hBel hBnorm
      hKbmem hB_rank hpY rfl hYcomp hcomm𝓛 htrans
      ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀, hb₀B, hb₀1, hJb₀⟩
    rw [hI22']
    refine sSup_le ?_
    rintro Z ⟨b, hb, hb1, hJ, rfl⟩
    exact hLayer b hb hb1 hJ
  have hKM' : barX p (Cg a) K ≤ barX p (Cg a) M := le_trans (le_sSup hKbmem) hYM
  apply hKM
  intro k hk
  obtain ⟨m, hm, hmk⟩ := exists_of_barX_le hKM' hk (hK.1 hk)
  have hmM : m⁻¹ * k ∈ M := h111 hSec ha ha1 hmk
  have := M.mul_mem hm hmM
  simpa using this

theorem J_good119 {p : ℕ} {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (hp : p.Prime) (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hK : GLAPComponent p (Cg a) K) (hKM : ¬ K ≤ M)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1)
    (hK18 : (p = 5 ∧ IsSporType .Fi22 (barOf p K)) ∨
      (p = 3 ∧ IsLThreeFour (barOf p K ⧸ Subgroup.center (barOf p K))))
    (h111 : Prop111Statement) (hI22 : Input22_3_2) (hI18 : Input18_3_diag) (hNB : NotBalanced119)
    (hord : Input_order_dvd) (hcent : Input_Fi22_centreless) (hnot : Input_not_LTwoTwentySeven)
    (h115 : Prop115Statement)
    {x : G} (hxA : x ∈ E ⊓ A) (hx1 : x ≠ 1) (hxC : x ∈ Cg a) :
    x ∈ Subgroup.normalizer (K : Set G) ∧
      ¬ (∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hxC⟩ * q =
        q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hxC⟩) := by
  have hno := no_bad119 hp hSec ha ha1 hK hKM hnotD hK18 h111 hI22 hI18 hNB hord hcent hnot h115
  have h2 : ¬ (x ∉ Subgroup.normalizer (K : Set G) ∨
      ∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hxC⟩ * q =
        q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hxC⟩) :=
    fun hc => hno ⟨⟨x, hxC⟩, hxA, hx1, hc⟩
  refine ⟨?_, fun hall => h2 (Or.inr hall)⟩
  by_contra hN
  exact h2 (Or.inl hN)

theorem inner_typec119 (hI23 : Input23_20_W) (h112 : Prop112Statement) (h111 : Prop111Statement)
    (h115 : Prop115Statement) (hNB : NotBalanced119) (hnot : Input_not_LTwoTwentySeven)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (hSec : Sec11 G m 3 B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD 3 M A1 ∧ a ∈ A1)
    (hK : GLAPComponent 3 (Cg a) K) (hKM : ¬ K ≤ M)
    (hL34 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hA0el : IsElemAbelian 3 (E ⊓ A)) (hA0C : E ⊓ A ≤ Cg a)
    (hA0N : E ⊓ A ≤ Subgroup.normalizer (K : Set G))
    (hrank : CFSG.Open.pRank 3 (E ⊓ A) = 2) :
    ∀ x ∈ E ⊓ A, InducesInner 3 K x := by
  by_contra hcon
  have hK1 : K ≤ Cg a := hK.1
  have hsnKC : IsSubnormal K (Cg a) := hK.2.1
  obtain ⟨hW, hmom⟩ := hI23 G (Cg a) K (E ⊓ A) hK hL34 hA0C hA0el hrank hA0N hcon
  apply hKM
  refine le_trans hW (sup_le (iSup₂_le fun x hx => ?_) ?_)
  ·
    obtain ⟨hxA, hx1⟩ := hx
    have hxC : x ∈ Cg a := hA0C hxA
    have hcg2 : Subgroup.centralizer ({x, a} : Set G) = Cg a ⊓ Subgroup.centralizer ({x} : Set G) :=
      l119_cg2_eq a x
    refine sup_le ?_ ?_
    ·
      have hsub : IsSubnormal (K ⊓ Subgroup.centralizer ({x} : Set G)) (Cg a ⊓ Subgroup.centralizer ({x} : Set G)) :=
        isSubnormal_inf hsnKC _
      have hcore : GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) ≤
          GLAPPrimeCoreOf 3 (Cg a ⊓ Subgroup.centralizer ({x} : Set G)) :=
        glaPPrimeCoreOf_le_of_isSubnormal (by norm_num) hsub
      have hM2 : GLAPPrimeCoreOf 3 (Cg2 x a) ≤ M := by
        rcases h112 hSec ha ha1 hxA hx1 with h | h
        · exact h
        · exact absurd h hnotD
      rw [Cg2, hcg2] at hM2
      exact hcore.trans hM2
    ·
      unfold GLAPLayer
      refine sSup_le fun Q hQ => ?_
      have hsubQ : IsSubnormal (K ⊓ Subgroup.centralizer ({x} : Set G)) (Cg a ⊓ Subgroup.centralizer ({x} : Set G)) :=
        isSubnormal_inf hsnKC _
      have hQ' : GLAPComponent 3 (Cg a ⊓ Subgroup.centralizer ({x} : Set G)) Q :=
        l119_glaPComponent_of_isSubnormal (by norm_num) hsubQ hQ
      have hJ : GLAPComponent 3 (Cg2 x a) Q := by
        rw [Cg2, hcg2]
        exact hQ'
      have hq := hmom x hxA hx1 Q hQ
      have hquasi := l119_isQuasisimple_barOf (p := 3) (by norm_num) hQ
      have h1 : ¬ IsLocallyOTwoBalancedWrtP 3 1 (barOf 3 Q) :=
        hNB _ 3 hquasi (glaPPrimeCore_quotient_eq_bot Nat.prime_three) (Or.inr ⟨rfl, hq⟩)
      have h2 : 3 = 3 → IsLTwoTwentySeven (barOf 3 Q) → ¬ IsCompLocallyOTwoBalanced 3 1 A Q := by
        intro _ hL27 _
        exact hnot (barOf 3 Q) hL27 (by
          rcases hq with hq | hq
          · exact Or.inl hq
          · exact Or.inr hq)
      rcases h115 hSec ha ha1 hxA hx1 hJ h1 h2 with hQM | ⟨A1, hA1, haA1⟩
      · exact hQM
      · exact absurd ⟨A1, hA1, haA1⟩ hnotD
  · exact (glaPPrimeCoreOf_le_of_isSubnormal (by norm_num) hsnKC).trans (h111 hSec ha ha1)

theorem lemma119_of_notBalanced (h118 : Lemma118Statement) (h111 : Prop111Statement)
    (h112 : Prop112Statement) (h115 : Prop115Statement) (hNB : NotBalanced119) (hI22 : Input22_3_2)
    (hI18 : Input18_3_diag) (hI23 : Input23_20_W) (hI7F : Input7_Fi22) (hI7L : Input7_L34)
    (hcent : Input_Fi22_centreless) (hord : Input_order_dvd) (hnot : Input_not_LTwoTwentySeven) :
    Lemma119Statement := by
  intro G _ _ m p B M E A a K h
  have hp : p.Prime := h.standing.prime
  have hSec : Sec11 G m p B M E A := h.toCex117Base.toSec11
  have ha : a ∈ A := h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have hK : GLAPComponent p (Cg a) K := h.hK
  have hKM : ¬ K ≤ M := h.notM
  have hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := h.notD
  obtain ⟨hAel, hrA0⟩ := l119_sec11_facts hSec
  have hK18 : Type117b p K ∨ Type117c p A K := h118 h
  have hK18' : (p = 5 ∧ IsSporType .Fi22 (barOf p K)) ∨
      (p = 3 ∧ IsLThreeFour (barOf p K ⧸ Subgroup.center (barOf p K))) := by
    rcases hK18 with ⟨h5, hb⟩ | ⟨h3, -, hl⟩
    · exact Or.inl ⟨h5, hb⟩
    · exact Or.inr ⟨h3, hl⟩
  have hACg : A ≤ Cg a := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨x, hx⟩)
  have hA0el : IsElemAbelian p (E ⊓ A) := l119_isElemAbelian_of_le inf_le_right hAel
  have hA0C : E ⊓ A ≤ Cg a := fun x hx => hACg hx.2
  have hgood : ∀ x (hxA : x ∈ E ⊓ A), x ≠ 1 →
      x ∈ Subgroup.normalizer (K : Set G) ∧
        ¬ (∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hACg hxA.2⟩ * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hACg hxA.2⟩) :=
    fun x hxA hx1 => J_good119 hp hSec ha ha1 hK hKM hnotD hK18' h111 hI22 hI18 hNB hord hcent hnot
      h115 hxA hx1 (hACg hxA.2)
  have hA0N : E ⊓ A ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · exact (hgood x hx hx1).1
  let φ := (CFSG.HardMathSupport.Solomon.LocalBalance.barAut p K).comp (Subgroup.inclusion hA0N)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hne
    have hx' : (x : G) ≠ 1 := fun h => hne (Subtype.ext h)
    have hbar : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p K ⟨(x : G), hA0N x.2⟩ = 1 := hx
    obtain ⟨hxN, hnc⟩ := hgood (x : G) x.2 hx'
    exact hnc (l119_centralizes_of_barAut hp hK (hACg x.2.2) hxN hbar)
  have hrank_le : CFSG.Open.pRank p (E ⊓ A) ≤ 2 := by
    rcases hK18' with ⟨h5, hF⟩ | ⟨h3, hL⟩
    · subst h5
      exact l119_pRank_le_two_of_inj hp hA0el φ hφinj (fun A' hA' => (hI7F _ hF).2 A' hA')
    · subst h3
      have hquasi := l119_isQuasisimple_barOf (p := 3) hp hK
      have hO := glaPPrimeCore_quotient_eq_bot (p := 3) hp (Z := ↥K)
      exact l119_pRank_le_two_of_inj hp hA0el φ hφinj
        (fun A' hA' => hI7L (barOf 3 K) hquasi hL hO A' hA')
  have hrank : CFSG.Open.pRank p (E ⊓ A) = 2 := le_antisymm hrank_le hrA0
  have hinner : ∀ x ∈ E ⊓ A, InducesInner p K x := by
    rcases hK18' with ⟨h5, hF⟩ | ⟨h3, hL⟩
    · subst h5
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        unfold centBar
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨1, ?_, ?_⟩, trivial⟩
        · exact MonoidHom.mem_ker.2 (map_one _)
        · simp
      · have hxN := hA0N hx
        have hpow : (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 5 K ⟨x, hxN⟩) ^ 5 = 1 := by
          rw [← map_pow]
          have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 5 = 1 := by
            apply Subtype.ext
            simpa using hAel.2 x hx.2
          rw [this, map_one]
        exact l119_inducesInner_of_inner hxN ((hI7F _ hF).1 _ (l119_isPGroup_zpowers hpow))
    · subst h3
      exact inner_typec119 hI23 h112 h111 h115 hNB hnot hSec ha ha1 hnotD hK hKM hL hA0el hA0C
        hA0N hrank
  refine ⟨hrank, ?_⟩
  unfold InducesFaithfulInner
  refine ⟨hA0N, ?_, hinner⟩
  intro x hx hc
  by_contra hx1
  obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hc).1
  have hbar : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p K ⟨x, hA0N hx⟩ = 1 := by
    have hxγ : (⟨x, hA0N hx⟩ : ↥(Subgroup.normalizer (K : Set G))) = γ := Subtype.ext hγx.symm
    rw [hxγ]
    exact MonoidHom.mem_ker.1 hγ
  obtain ⟨_, hnc⟩ := hgood x hx hx1
  exact hnc (l119_centralizes_of_barAut hp hK (hACg hx.2) (hA0N hx) hbar)

end L119

theorem lemma119_of_notBalanced''
    (h118 : Lemma118Statement) (h111 : Prop111Statement)
    (h112 : Prop112Statement) (h115 : Prop115Statement) (hNB : NotBalanced119)
    (hI23 : Input23_20_W) (hI7F : Input7_Fi22) (hI7L : Input7_L34) : Lemma119Statement :=
  lemma119_of_notBalanced h118 h111 h112 h115 hNB input22_3_2_holds input18_3_diag_holds hI23 hI7F hI7L
    Input_Fi22_centreless_holds Input_order_dvd_holds Input_not_LTwoTwentySeven_holds

theorem lemma119_of_core
    (h118 : Lemma118Statement) (h111 : Prop111Statement) (h112 : Prop112Statement)
    (h115 : Prop115Statement) (hSpor : Input1919.Input19_19Spor) (hI23 : Input23_20_W)
    (hI7F : Input7_Fi22) (hI7L : Input7_L34) : Lemma119Statement :=
  lemma119_of_notBalanced'' h118 h111 h112 h115 (notBalanced119_of_spor hSpor) hI23 hI7F hI7L

@[expose] def NotBalanced126 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
    ((∃ n : ℕ, 5 ≤ n ∧ n % 3 = 1 ∧ IsAltType n (X ⧸ Subgroup.center X)) ∨
      IsLpType 2 7 (X ⧸ Subgroup.center X) ∨ IsSporType .He (X ⧸ Subgroup.center X)) →
    ¬ IsLocallyOTwoBalancedWrtP 3 1 X

theorem notBalanced126_of_spor
    (hSpor : Input1919.Input19_19Spor) : NotBalanced126 := by
  intro X _ _ hq h
  rcases h with ⟨n, hn5, hn1, hA⟩ | hL | hHe
  · exact Input1919.not_balanced_alt_four Nat.prime_three (by norm_num) hn5 hA (by omega)
  · exact Input1919.not_balanced_L27 hq hL
  · exact (hSpor X hq).2 hHe

structure Inp126' : Prop where
  i18_3 : Prop115.Input18_3Gen
  i18_3_2 : Prop126.Input18_3_2
  i14_15_3 : Prop126.Input14_15_3
  i22_3_2 : Input22_3_2
  i18_diag : Input18_3_diag
  i19_19 : NotBalanced126
  notL227 : Prop126b.NotL227
  altCentre : Prop126b.InputAltCentre
  heCent : Prop126b.InputHeCent
  heGen : Prop126b.InputHeGen
  anCent : Prop126b.InputAnCent
  i23_7 : Prop126b.Input23_7_amb
  setup : Prop126b.Setup126

section P126

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {J : Subgroup G}
  {z : G} {J₀ : Subgroup G} (c : Prop126b.Cex126 G m B M E A a J z J₀)

include c

theorem he_final126 (sib : Prop126b.Sib126) (inp : Inp126') {L : Subgroup G} (hL : GLAPComponent 3 (Cg a) L)
    (hLM : ¬ L ≤ M) (hgood : Prop126b.Good126 E A a L)
    (hHe : IsSporType .He (↥(barX 3 (Cg a) L) ⧸ Subgroup.center ↥(barX 3 (Cg a) L))) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLC : L ≤ Cg a := hL.1
  have hKq : CFSG.Open.IsQuasisimple ↥(barX 3 (Cg a) L) := hL.2.2.1.2.2
  let Ty : ∀ (X : Type) [Group X], Prop := fun X _ => IsLpType 2 7 X ∨ IsAltType 7 X
  have hTyiso : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → Ty X → Ty Y := by
    intro X Y _ _ e h
    rcases h with h | h
    · exact Or.inl (Prop126b.isLpType_congr e h)
    · exact Or.inr (l119_isAltType_congr 7 e h)
  have hnb : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
      Ty (X ⧸ Subgroup.center X) → ¬ IsLocallyOTwoBalancedWrtP 3 1 X ∧ ¬ IsLTwoTwentySeven X := by
    intro X _ _ hX hTy
    rcases hTy with h | h
    · exact ⟨inp.i19_19 X hX (Or.inr (Or.inl h)),
        fun hL => (inp.notL227 X hL).2.2 h⟩
    · exact ⟨inp.i19_19 X hX (Or.inl ⟨7, by norm_num, by norm_num, h⟩),
        fun hL => (inp.notL227 X hL).1 7 (by norm_num) h⟩
  have hlayer : ∀ e ∈ E ⊓ A, e ≠ 1 → ∀ heC : e ∈ Cg a,
      GLAPLayer 3 (barX 3 (Cg a) L ⊓ Subgroup.centralizer
        ({Prop126b.bar3 a e heC} : Set (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)))) ≤ barX 3 (Cg a) M := by
    intro e he he1 heC
    obtain ⟨heC', hnorm, q, hq, hqne⟩ := hgood e he he1
    refine c.layer_le_M_bar sib.h115 Ty hTyiso hnb hL he he1 heC ?_
    intro Q hQ
    refine inp.heCent _ (barX 3 (Cg a) L) hKq hHe (Prop126b.bar3 a e heC)
      (Prop126b.bar3_mem_normalizer hLC heC hnorm) ?_ ⟨q, hq, hqne⟩ Q hQ
    refine orderOf_eq_prime (c.bar_pow he heC) ?_
    intro h1
    apply hqne
    rw [h1, one_mul, mul_one]
  have hBnorm : barX 3 (Cg a) (E ⊓ A) ≤ Subgroup.normalizer
      ((barX 3 (Cg a) L : Subgroup _) : Set _) := by
    intro b hb
    obtain ⟨e, he, heC, rfl⟩ := c.exists_of_mem_bar hb
    by_cases he1 : e = 1
    · subst he1
      have : Prop126b.bar3 a 1 heC = 1 := by
        show QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) ⟨1, heC⟩ = 1
        exact map_one _
      rw [this]
      exact Subgroup.one_mem _
    · obtain ⟨heC', hnorm, -⟩ := hgood e he he1
      exact Prop126b.bar3_mem_normalizer hLC heC hnorm
  have hfaith : ∀ b ∈ barX 3 (Cg a) (E ⊓ A), b ≠ 1 → ∃ q ∈ barX 3 (Cg a) L, b * q ≠ q * b := by
    intro b hb hb1
    obtain ⟨e, he, heC, rfl⟩ := c.exists_of_mem_bar hb
    have he1 : e ≠ 1 := by
      rintro rfl
      apply hb1
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) ⟨1, heC⟩ = 1
      exact map_one _
    obtain ⟨heC', -, q, hq, hqne⟩ := hgood e he he1
    exact ⟨q, hq, hqne⟩
  have hgen := inp.heGen _ (barX 3 (Cg a) L) (barX 3 (Cg a) (E ⊓ A)) hKq hHe hBnorm
    c.bar_elemAbelian c.bar_rank hfaith
  have hle : barX 3 (Cg a) L ≤ barX 3 (Cg a) M := by
    refine hgen.trans (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_)
    obtain ⟨e, he, heC, rfl⟩ := c.exists_of_mem_bar hb
    have he1 : e ≠ 1 := by
      rintro rfl
      apply hb1
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) ⟨1, heC⟩ = 1
      exact map_one _
    exact hlayer e he he1 heC
  exact hLM (c.le_M_of_barX_le sib.h111 hLC hle)

theorem an_final126 (sib : Prop126b.Sib126) (inp : Inp126') {L : Subgroup G} (hL : GLAPComponent 3 (Cg a) L)
    (hzL : z ∈ Subgroup.normalizer (L : Set G)) (hJ₀L : GLAPComponent 3 (L ⊓ Cg z) J₀)
    (hLM : ¬ L ≤ M) (hgood : Prop126b.Good126 E A a L) {k : ℕ} (hk : 1 ≤ k)
    (hAn : IsAltType (7 + 3 * k) (↥(barX 3 (Cg a) L) ⧸ Subgroup.center ↥(barX 3 (Cg a) L))) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLC : L ≤ Cg a := hL.1
  have hKbc : IsComponentOf (barX 3 (Cg a) L) ⊤ := hL.2.2.1
  have hKq : CFSG.Open.IsQuasisimple ↥(barX 3 (Cg a) L) := hKbc.2.2
  have hKcore : GLAPPrimeCore 3 ↥(barX 3 (Cg a) L) = ⊥ :=
    Prop126b.primeCore_sub_eq_bot Nat.prime_three (glaPPrimeCore_quotient_eq_bot Nat.prime_three) hKbc.2.1
  have hAnK : IsAltType (7 + 3 * k) ↥(barX 3 (Cg a) L) :=
    inp.altCentre _ (7 + 3 * k) (by omega) hKq hKcore hAn
  let Ty : ∀ (X : Type) [Group X], Prop := fun X _ => ∃ r : ℕ, 5 ≤ r ∧ r % 3 = 1 ∧ IsAltType r X
  have hTyiso : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → Ty X → Ty Y := by
    rintro X Y _ _ e ⟨r, h5, h3, h⟩
    exact ⟨r, h5, h3, l119_isAltType_congr r e h⟩
  have hnb : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
      Ty (X ⧸ Subgroup.center X) → ¬ IsLocallyOTwoBalancedWrtP 3 1 X ∧ ¬ IsLTwoTwentySeven X := by
    rintro X _ _ hX ⟨r, h5, h3, h⟩
    exact ⟨inp.i19_19 X hX (Or.inl ⟨r, h5, h3, h⟩),
      fun hL => (inp.notL227 X hL).1 r h5 h⟩
  have hBnorm := c.hBnorm_of_good hLC hgood
  have hfaith := c.hfaith_of_good hgood
  have hnontriv : ∀ e (he : e ∈ E ⊓ A) (he1 : e ≠ 1) (heC : e ∈ Cg a),
      ∃ q ∈ barX 3 (Cg a) L, Prop126b.bar3 a e heC * q ≠ q * Prop126b.bar3 a e heC := by
    intro e he he1 heC
    obtain ⟨heC', -, q, hq, hqne⟩ := hgood e he he1
    exact ⟨q, hq, hqne⟩
  have hlayer : ∀ e ∈ E ⊓ A, e ≠ 1 → ∀ heC : e ∈ Cg a,
      GLAPLayer 3 (barX 3 (Cg a) L ⊓ Subgroup.centralizer
        ({Prop126b.bar3 a e heC} : Set (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)))) ≤ barX 3 (Cg a) M := by
    intro e he he1 heC
    obtain ⟨heC', hnorm, hq⟩ := hgood e he he1
    refine c.layer_le_M_bar sib.h115 Ty hTyiso hnb hL he he1 heC ?_
    intro Q hQ
    exact inp.anCent _ (barX 3 (Cg a) L) (7 + 3 * k) (by omega) (by omega) hKq hAn (Prop126b.bar3 a e heC)
      (Prop126b.bar3_mem_normalizer_aux hLC heC hnorm)
      (orderOf_eq_prime (c.bar_pow he heC) (by
        rintro h1
        obtain ⟨q, hq', hqne⟩ := hq
        apply hqne
        rw [h1, one_mul, mul_one])) hq Q hQ
  have hpcore : ∀ e ∈ E ⊓ A, e ≠ 1 → ∀ heC : e ∈ Cg a,
      GLAPPrimeCoreOf 3 (barX 3 (Cg a) L ⊓ Subgroup.centralizer
        ({Prop126b.bar3 a e heC} : Set (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)))) ≤ barX 3 (Cg a) M := by
    intro e he he1 heC
    obtain ⟨heC', hnorm, -⟩ := hgood e he he1
    exact c.primeCore_le_M_bar sib.h112 hL he he1 heC hnorm
  have hW : (⨆ (b : ↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)) (_ : b ∈ barX 3 (Cg a) (E ⊓ A)) (_ : b ≠ 1),
      (GLAPPrimeCoreOf 3 (barX 3 (Cg a) L ⊓ Subgroup.centralizer ({b} : Set _)) ⊔
        GLAPLayer 3 (barX 3 (Cg a) L ⊓ Subgroup.centralizer ({b} : Set _)))) ≤
      barX 3 (Cg a) M := by
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    obtain ⟨e, he, heC, rfl⟩ := c.exists_of_mem_bar hb
    have he1 : e ≠ 1 := by
      rintro rfl
      apply hb1
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) ⟨1, heC⟩ = 1
      exact map_one _
    exact sup_le (hpcore e he he1 heC) (hlayer e he he1 heC)
  have hzC := c.zC
  have hz1 : z ≠ 1 := by
    intro h1
    have := c.hz3
    rw [h1, orderOf_one] at this
    omega
  have hd : IsPGroup 3 (Subgroup.zpowers z) := l119_isPGroup_zpowers (by
    rw [← c.hz3]
    exact pow_orderOf_eq_one z)
  have hJb := Prop126b.glaPComponent_barX_inf_centralizer (p := 3) Nat.prime_three (M := Cg a) hzC hLC hzL hd hJ₀L
  have hJbty : IsAltType 7 (Prop126b.barZ3 (barX 3 (Cg a) J₀)) := by
    have e := Prop126b.barOfBarX Nat.prime_three c.hJ₀C
    refine Prop126b.isAltType_seven_quot_center ?_
    rcases c.ty3 with h | h
    · exact Or.inl (l119_isAltType_congr 7 e h)
    · exact Or.inr (sec9_isHatSeven_of_mulEquiv e h)
  have hzB : Prop126b.bar3 a z hzC ∈ barX 3 (Cg a) (E ⊓ A) :=
    ⟨⟨z, hzC⟩, (Subgroup.mem_subgroupOf).2 c.hz, rfl⟩
  have hzb1 : Prop126b.bar3 a z hzC ≠ 1 := by
    intro h1
    obtain ⟨heC', -, q, hq, hqne⟩ := hgood z c.hz hz1
    apply hqne
    rw [h1, one_mul, mul_one]
  have hdiv := inp.i23_7 _ (barX 3 (Cg a) L) (barX 3 (Cg a) (E ⊓ A)) (7 + 3 * k) (by omega) (by omega)
    hAnK hBnorm c.bar_elemAbelian hfaith (Prop126b.bar3 a z hzC) hzB hzb1 (barX 3 (Cg a) J₀) hJb hJbty _ rfl _ rfl
    (c.central_product sib hW rfl)
  rw [rank_barX_of_isPGroup Nat.prime_three c.hA0p c.hA0C] at hdiv
  have hn : IsAltType (7 + 3 * k) (barOf 3 L) :=
    l119_isAltType_congr _ (quotEquivBarX Nat.prime_three hLC hL.2.1).symm hAnK
  exact Prop126.an_branch_false c.sec sib.h117 c.ha c.ha1 c.hnD hL hLM hn (by omega) (by omega) hdiv

theorem core_single126 (sib : Prop126b.Sib126) (inp : Inp126') {L : Subgroup G} (hL : GLAPComponent 3 (Cg a) L)
    (hzL : z ∈ Subgroup.normalizer (L : Set G)) (hJ₀L : GLAPComponent 3 (L ⊓ Cg z) J₀) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLC : L ≤ Cg a := hL.1
  have hJ₀L' : J₀ ≤ L := hJ₀L.1.trans inf_le_left
  have hLM : ¬ L ≤ M := fun h =>
    c.key {L} (by simpa using hL) (by simpa using h) (by simpa using hJ₀L')
  by_cases hact : ∃ q ∈ barX 3 (Cg a) L, Prop126b.bar3 a z c.zC * q ≠ q * Prop126b.bar3 a z c.zC
  · have hty := Prop126b.pumpup_type inp.i14_15_3 c.hkp c.hCtop c.zC c.hz3' hL hzL hJ₀L c.ty3 hact
    let Ty : ∀ (X : Type) [Group X], Prop := fun X _ =>
      IsSporType .He X ∨ ∃ k : ℕ, 1 ≤ k ∧ IsAltType (7 + 3 * k) X
    have hTyiso : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → Ty X → Ty Y := by
      intro X Y _ _ e h
      rcases h with h | ⟨k, hk, h⟩
      · exact Or.inl (l119_isSporType_congr _ e h)
      · exact Or.inr ⟨k, hk, l119_isAltType_congr _ e h⟩
    have hnb : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
        Ty (X ⧸ Subgroup.center X) → ¬ IsLocallyOTwoBalancedWrtP 3 1 X ∧ ¬ IsLTwoTwentySeven X := by
      intro X _ _ hX hTy
      rcases hTy with h | ⟨k, hk, h⟩
      · exact ⟨inp.i19_19 X hX (Or.inr (Or.inr h)),
          fun hL => (inp.notL227 X hL).2.1 h⟩
      · exact ⟨inp.i19_19 X hX (Or.inl ⟨7 + 3 * k, by omega, by omega, h⟩),
          fun hL => (inp.notL227 X hL).1 (7 + 3 * k) (by omega) h⟩
    have hpK : 3 ∣ Nat.card ↥(barX 3 (Cg a) L) :=
      (Prop126b.three_dvd_card_barX c.hJ₀C c.three_dvd_J₀).trans
        (Subgroup.card_dvd_of_le (barX_mono hJ₀L'))
    have hKTy : Ty ((↥L ⧸ GLAPPrimeCore 3 ↥L) ⧸ Subgroup.center (↥L ⧸ GLAPPrimeCore 3 ↥L)) :=
      hTyiso _ _ (l119_centerQuot_equiv (quotEquivBarX Nat.prime_three hLC hL.2.1).symm) hty
    have hnobad := Prop126b.no_bad_gen (p := 3) Nat.prime_three Ty hTyiso hnb c.sec c.ha c.ha1 hL hLM hpK
      (fun ⟨A1, hA1, haA1⟩ => c.hnD A1 hA1 haA1) hKTy sib.h111 inp.i22_3_2 inp.i18_diag sib.h115
    have hgood : Prop126b.Good126 E A a L := by
      intro e he he1
      have heC : e ∈ Cg a := c.hA0C he
      refine ⟨heC, ?_, ?_⟩
      · by_contra hn
        exact hnobad ⟨⟨e, heC⟩, he, he1, Or.inl hn⟩
      · by_contra hq
        push Not at hq
        exact hnobad ⟨⟨e, heC⟩, he, he1, Or.inr fun q hq' => hq q hq'⟩
    rcases hty with hHe | ⟨k, hk, hAn⟩
    · exact he_final126 c sib inp hL hLM hgood hHe
    · exact an_final126 c sib inp hL hzL hJ₀L hLM hgood hk hAn
  · push Not at hact
    exact hLM (c.le_M_of_central_action sib.h111 hL hzL hJ₀L hact)

theorem core_cycled126 (sib : Prop126b.Sib126) (inp : Inp126') {L : ZMod 3 → Subgroup G}
    (hL : ∀ i, GLAPComponent 3 (Cg a) (L i)) (hinj : Function.Injective L)
    (hcyc : ∀ i, GLBConj z (L i) = L (i + 1))
    (hJ₀L : GLAPComponent 3 ((⨆ i, L i) ⊓ Cg z) J₀) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLC : ∀ i, L i ≤ Cg a := fun i => (hL i).1
  have hJ₀S : J₀ ≤ ⨆ i, L i := hJ₀L.1.trans inf_le_left
  have hLM : ∀ i, ¬ L i ≤ M := by
    intro i hi
    have hstep : ∀ j, L j ≤ M → L (j + 1) ≤ M := by
      intro j hj
      rw [← hcyc j]
      have hM : GLBConj z M = M := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer c.hzM)
      calc GLBConj z (L j) ≤ GLBConj z M := gLBConj_mono z hj
        _ = M := hM
    have hn : ∀ n : ℕ, L (i + (n : ZMod 3)) ≤ M := by
      intro n
      induction n with
      | zero => simpa using hi
      | succ n ih =>
        have := hstep _ ih
        simpa [add_assoc, Nat.cast_succ] using this
    have hall : ∀ j, L j ≤ M := by
      intro j
      have : i + (((j - i).val : ℕ) : ZMod 3) = j := by
        rw [ZMod.natCast_zmod_val]
        exact add_sub_cancel i j
      rw [← this]
      exact hn _
    have hrange : (⨆ L' ∈ Set.range L, L') = ⨆ i, L i := by
      apply le_antisymm
      · exact iSup₂_le (by rintro _ ⟨i, rfl⟩; exact le_iSup L i)
      · exact iSup_le fun i => le_iSup₂_of_le (L i) ⟨i, rfl⟩ le_rfl
    exact c.key (Set.range L) (by rintro _ ⟨j, rfl⟩; exact hL j) (by rintro _ ⟨j, rfl⟩; exact hall j)
      (by rw [hrange]; exact hJ₀S)
  have hd : IsPGroup 3 (Subgroup.zpowers z) := l119_isPGroup_zpowers c.hz3'
  have hzJ : z ∈ Subgroup.normalizer ((⨆ i, L i : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq]
    unfold GLBConj
    rw [Subgroup.map_iSup]
    have h1 : ∀ i, (L i).map (MulAut.conj z⁻¹).toMonoidHom = L (i + 1) := hcyc
    simp only [h1]
    exact (Equiv.addRight (1 : ZMod 3)).iSup_comp (g := L)
  have hQ := Prop126b.glaPComponent_barX_inf_centralizer (p := 3) Nat.prime_three (M := Cg a) c.zC
    (iSup_le hLC) hzJ hd hJ₀L
  let Kbs : ZMod 3 → Subgroup (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)) := fun i => barX 3 (Cg a) (L i)
  have h𝓛c : ∀ X ∈ Set.range Kbs, IsComponentOf X ⊤ := by
    rintro _ ⟨i, rfl⟩
    exact (hL i).2.2.1
  have hcomm : ∀ X ∈ Set.range Kbs, ∀ X' ∈ Set.range Kbs, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X',
      x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne x hx y hy
    exact comp_comm (h𝓛c _ ⟨i, rfl⟩) (h𝓛c _ ⟨j, rfl⟩) hne hx hy
  have hsSup : sSup (Set.range Kbs) = barX 3 (Cg a) (⨆ i, L i) := by
    rw [Prop126b.barX_iSup_eq 3 L hLC, sSup_range]
  have hQ' : GLAPComponent 3 (sSup (Set.range Kbs) ⊓ Subgroup.centralizer
      ({Prop126b.bar3 a z c.zC} : Set (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)))) (barX 3 (Cg a) J₀) := by
    rw [hsSup]
    exact hQ
  have hzN : Prop126b.bar3 a z c.zC ∈ Subgroup.normalizer ((sSup (Set.range Kbs) : Subgroup _) : Set _) := by
    rw [hsSup]
    exact Prop126b.bar3_mem_normalizer_aux (iSup_le hLC) c.zC hzJ
  have hnotnorm : ∀ i, z ∉ Subgroup.normalizer (L i : Set G) := by
    intro i hz
    have h1 := hcyc i
    rw [mem_normalizer_iff_gLBConj_eq.1 hz] at h1
    have := hinj h1
    have h2 : (i : ZMod 3) + 1 ≠ i := by
      intro h
      have h3 := add_eq_left.1 h
      exact Prop126b.zmod3_one_ne_zero h3
    exact h2 this.symm
  have hzbord : orderOf (Prop126b.bar3 a z c.zC) = 3 := by
    refine orderOf_eq_prime (c.bar_pow c.hz c.zC) ?_
    intro h1
    have h2 : (⟨z, c.zC⟩ : ↥(Cg a)) = 1 := by
      apply l119_eq_one_of_pow_of_mem_core Nat.prime_three
        (Subtype.ext (by simpa using c.hz3'))
      exact (QuotientGroup.eq_one_iff _).1 h1
    exact c.hz1 (congrArg Subtype.val h2)
  have hdich : Prop126b.bar3 a z c.zC ∈ Subgroup.centralizer ((sSup (Set.range Kbs) : Subgroup _) : Set _) ∨
      ∀ X ∈ Set.range Kbs, Prop126b.bar3 a z c.zC ∉ Subgroup.normalizer (X : Set _) := by
    right
    rintro _ ⟨i, rfl⟩ hmem
    exact hnotnorm i (l119_mem_normalizer_of_bar Nat.prime_three (hL i) ⟨z, c.zC⟩ hmem)
  obtain ⟨X, ⟨i₀, rfl⟩, ⟨e⟩⟩ := inp.i18_diag _ 3 Nat.prime_three (sSup (Set.range Kbs))
    (Set.range Kbs) (Prop126b.bar3 a z c.zC) hzbord hzN rfl
    (fun X hX => l119_isComponentOf_sSup h𝓛c hcomm hX) hcomm hdich _ hQ'
  have hJbty : IsAltType 7 (Prop126b.barZ3 (barX 3 (Cg a) J₀)) := by
    have e' := Prop126b.barOfBarX Nat.prime_three c.hJ₀C
    refine Prop126b.isAltType_seven_quot_center ?_
    rcases c.ty3 with h | h
    · exact Or.inl (l119_isAltType_congr 7 e' h)
    · exact Or.inr (sec9_isHatSeven_of_mulEquiv e' h)
  have hX7 : IsAltType 7 (↥(Kbs i₀) ⧸ Subgroup.center ↥(Kbs i₀)) :=
    l119_isAltType_congr 7 e hJbty
  have hKTy : IsAltType 7 ((↥(L i₀) ⧸ GLAPPrimeCore 3 ↥(L i₀)) ⧸
      Subgroup.center (↥(L i₀) ⧸ GLAPPrimeCore 3 ↥(L i₀))) :=
    l119_isAltType_congr 7 (l119_centerQuot_equiv (quotEquivBarX Nat.prime_three (hLC i₀) (hL i₀).2.1)).symm
      hX7
  have hpK : 3 ∣ Nat.card ↥(barX 3 (Cg a) (L i₀)) :=
    (Prop126b.three_dvd_of_isAltType_seven hX7).trans (Subgroup.card_quotient_dvd_card _)
  let Ty : ∀ (X : Type) [Group X], Prop := fun X _ => IsAltType 7 X
  have hTyiso : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → Ty X → Ty Y :=
    fun X Y _ _ e h => l119_isAltType_congr 7 e h
  have hnb : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
      Ty (X ⧸ Subgroup.center X) → ¬ IsLocallyOTwoBalancedWrtP 3 1 X ∧ ¬ IsLTwoTwentySeven X := by
    intro X _ _ hX h
    exact ⟨inp.i19_19 X hX (Or.inl ⟨7, by norm_num, by norm_num, h⟩),
      fun hL => (inp.notL227 X hL).1 7 (by norm_num) h⟩
  have hnobad := Prop126b.no_bad_gen (p := 3) Nat.prime_three Ty hTyiso hnb c.sec c.ha c.ha1 (hL i₀)
    (hLM i₀) hpK (fun ⟨A1, hA1, haA1⟩ => c.hnD A1 hA1 haA1) hKTy sib.h111 inp.i22_3_2
    inp.i18_diag sib.h115
  exact hnobad ⟨⟨z, c.zC⟩, c.hz, c.hz1, Or.inl (hnotnorm i₀)⟩

theorem core126 (sib : Prop126b.Sib126) (inp : Inp126') : False := by
  have hsimp : IsSimpleGroup G := c.sec.standing.simple
  have hnab := c.sec.standing.nonabelian
  rcases Prop126.jstar3_dichotomy hsimp hnab c.hkp inp.i18_3 inp.i18_3_2 c.hz3 c.a3 c.hza c.hJ₀ with
    ⟨L, hL, hJL, hzL, hJ₀L⟩ | ⟨L, hL, hinj, hcyc, hJL, hJ₀L⟩
  · rw [hJL] at hJ₀L
    exact core_single126 c sib inp hL (mem_normalizer_iff_gLBConj_eq.2 hzL) hJ₀L
  · rw [hJL] at hJ₀L
    exact core_cycled126 c sib inp hL hinj hcyc hJ₀L

end P126

theorem prop126_of_notBalanced (sib : Prop126b.Sib126) (inp : Inp126') : Prop126Statement := by
  unfold Prop126Statement
  intro G _ _ m B M E A h a ha ha1 J hJ
  by_cases hD : ∃ A₁ : Subgroup G, inD 3 M A₁ ∧ a ∈ A₁
  · obtain ⟨A₁, hA₁, haA₁⟩ := hD
    exact Prop126.of_mem_inD hA₁ haA₁ ha1 hJ
  push Not at hD
  by_contra hcon
  have hnot : ¬ IsSubnormal J (Cg a) := fun hsn =>
    hcon (isTwoPrimeComp_of_le hJ inf_le_right hsn)
  obtain ⟨R, z, hR, hER, hzR, hzEA, hzα, hz3⟩ :=
    Prop126b.exists_z_R h (Prop126b.three_dvd_alpha hJ)
  obtain ⟨J₀, hJ₀, hJ₀J, hcov, ty2, ty3⟩ := inp.setup h ha ha1 hD hJ hR hER hzR hzα hz3
  exact core126 ⟨h, ha, ha1, hD, hJ, hnot, hzEA, hz3, hJ₀, hJ₀J, hcov, ty2, ty3⟩ sib inp

theorem prop126_of_spor'
    (sib : Prop126b.Sib126) (hSpor : Input1919.Input19_19Spor)
    (i18_3 : Prop115.Input18_3Gen) (i18_3_2 : Prop126.Input18_3_2) (i14_15_3 : Prop126.Input14_15_3)
    (i22_3_2 : Input22_3_2) (i18_diag : Input18_3_diag) (notL227 : Prop126b.NotL227)
    (altCentre : Prop126b.InputAltCentre) (heCent : Prop126b.InputHeCent) (heGen : Prop126b.InputHeGen)
    (anCent : Prop126b.InputAnCent) (i23_7 : Prop126b.Input23_7_amb) (setup : Prop126b.Setup126) :
    Prop126Statement :=
  prop126_of_notBalanced sib ⟨i18_3, i18_3_2, i14_15_3, i22_3_2, i18_diag, notBalanced126_of_spor hSpor,
    notL227, altCentre, heCent, heGen, anCent, i23_7, setup⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input1919b

end
