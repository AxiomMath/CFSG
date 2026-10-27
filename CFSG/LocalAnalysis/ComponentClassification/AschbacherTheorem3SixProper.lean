module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixStrong
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightBenderCase

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem exists_odd_ext {G T N : Subgroup X} (hGn : G.Normal) (hNn : N.Normal) (hNG : N ≤ G)
    {S' : Subgroup (X ⧸ N)}
    (h42 : Hyp42 (G.map (QuotientGroup.mk' N)) (T.map (QuotientGroup.mk' N)) S') :
    ∃ K : Subgroup X, N ≤ K ∧ K ≤ G ∧ K.Normal ∧ ⁅G, T⁆ ≤ K ∧
      (∀ C ≤ K, ¬ 2 ∣ N.relIndex C) ∧ (∀ k ∈ K, ∀ e : ℕ, k ^ (2 ^ e) ∈ N → k ∈ N) := by
  set π := QuotientGroup.mk' N with hπ
  have hkerπ : π.ker = N := QuotientGroup.ker_mk' N
  have hcomm := lemma_4_2_oddCore h42
  set Kb : Subgroup (X ⧸ N) := (CFSG.oddCore (G.map π)).map (G.map π).subtype with hKb
  have hKbodd : Odd (Nat.card Kb) := by
    rw [hKb, Subgroup.card_map_of_injective (G.map π).subtype_injective]
    exact odd_card_oddCore _
  have hKbn : Kb.Normal := by
    have : (CFSG.oddCore (G.map π)).Characteristic := OddCore.characteristic _
    have hGbn : (G.map π).Normal := hGn.map π (QuotientGroup.mk'_surjective N)
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro y _
    exact mem_normalizer_map_of_characteristic _ (by
      rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top y)
  refine ⟨Kb.comap π, fun z hz => ?_, ?_, hKbn.comap π, ?_, ?_, ?_⟩
  · show π z ∈ Kb
    have h1 : π z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [h1]
    exact Kb.one_mem
  · intro x hx
    have h1 : π x ∈ G.map π := Subgroup.map_subtype_le _ hx
    have h2 := mk_mem_map_iff.mp h1
    rwa [sup_eq_left.mpr hNG] at h2
  · rw [Subgroup.commutator_le]
    intro x hx u hu
    show π (x * u * x⁻¹ * u⁻¹) ∈ Kb
    have : π (x * u * x⁻¹ * u⁻¹) = ⁅π x, π u⁆ := by
      simp only [map_mul, map_inv, commutatorElement_def]
    rw [this]
    exact hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem π hx)
      (Subgroup.mem_map_of_mem π hu))
  · intro C hC h2
    have hrel := Subgroup.relIndex_ker (K := C) π
    rw [hkerπ] at hrel
    rw [hrel] at h2
    have hdvd : Nat.card (C.map π) ∣ Nat.card Kb :=
      Subgroup.card_dvd_of_le (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact hC hx)
    exact (Nat.not_even_iff_odd.mpr hKbodd) (even_iff_two_dvd.mpr (h2.trans hdvd))
  · intro k hk e hke
    have hπk : π k ^ (2 ^ e) = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hke
    exact (QuotientGroup.eq_one_iff k).mp
      (eq_one_of_two_pow_of_odd (show π k ∈ Kb from hk) hKbodd hπk)

namespace Conf46

variable {G T S Q H : Subgroup X} {g : X}

theorem conj_le_sup_of_le (c : Conf46 G T S Q H g) {M : Subgroup X} (hMn : M.Normal)
    (hMG : M ≤ G) (hWM : T ⊔ rightConjugate T g ≤ T ⊔ M) {x : X} (hx : x ∈ G)
    (hle : rightConjugate T x ≤ S ⊔ M) : rightConjugate T x ≤ T ⊔ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSM : IsSylowOf 2 S (S ⊔ M) :=
    c.sylowFrame.sylow.of_le le_sup_left (sup_le c.le_sup (hMG.trans le_sup_left))
  obtain ⟨d, hd, hdle⟩ := exists_rightConjugate_le_of_isSylowOf hSM
    (isPGroup_rightConjugate c.frame.isPGroup x) hle
  have hdm : d ∈ (M : Set X) * (S : Set X) := by
    rw [← Subgroup.normal_mul, sup_comm]
    exact hd
  obtain ⟨m, hm, s, hs, rfl⟩ := Set.mem_mul.mp hdm
  have h1 : rightConjugate T (x * m) ≤ S := by
    have h2 := rightConjugate_le_rightConjugate hdle s⁻¹
    rwa [rightConjugate_mul, rightConjugate_mul, rightConjugate_eq_of_mem (S.inv_mem hs),
      mul_inv_cancel_right] at h2
  have h3 : rightConjugate T (x * m) ≤ T ⊔ rightConjugate T g := by
    rw [← c.weakClosure]
    exact rightConjugate_le_relativeWeakClosure (G.mul_mem hx (hMG hm)) h1
  have h4 := rightConjugate_le_rightConjugate (h3.trans hWM) m⁻¹
  rwa [rightConjugate_mul, mul_inv_cancel_right,
    rightConjugate_eq_of_mem (Subgroup.mem_sup_right (M.inv_mem hm))] at h4

theorem commutator_le_of_inner (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (hO : CFSG.oddCore G = ⊥) {M A : Subgroup X} (hMn : M.Normal) (hMG : M ≤ G)
    (hZM : (T ⊔ rightConjugate T g) ⊓ G ≤ M)
    (hcen : M ⊓ Subgroup.centralizer (M : Set X) = ⊥)
    (hAC : A ≤ Subgroup.centralizer (M : Set X)) (hTA : T ≤ A ⊔ M) : ⁅G, T⁆ ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  set π := QuotientGroup.mk' M with hπ
  have hWM : T ⊔ rightConjugate T g ≤ T ⊔ M := by
    rw [c.hyp45.W_decomp.1]
    exact sup_le_sup_left hZM T
  have hinjT : ∀ x : X, ∀ y ∈ rightConjugate T x, π y = 1 → y = 1 := by
    intro x y hy h1
    have hyM : y ∈ M := (QuotientGroup.eq_one_iff y).mp h1
    have hyT : y ∈ rightConjugate T x ⊓ rightConjugate G x := by
      refine ⟨hy, ?_⟩
      have hxN : x ∈ Subgroup.normalizer (G : Set X) := by
        rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x
      rw [(rightConjugate_eq_self_iff _ x).mpr hxN]
      exact hMG hyM
    rw [← rightConjugate_inf, c.frame.inf_eq_bot, rightConjugate_bot] at hyT
    exact hyT
  have hinjT₀ : ∀ y ∈ T, π y = 1 → y = 1 := fun y hy h1 =>
    hinjT 1 y (by rw [rightConjugate_one]; exact hy) h1
  have hMb : M.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have h42 : Hyp42 (G.map π) (T.map π) (S.map π) := by
    refine ⟨c.frame.map M hMG, ?_, Subgroup.map_mono c.le_S, ?_⟩
    · rw [← Subgroup.map_sup]
      exact IsSylowOf.map c.sylowFrame.sylow π
    · rintro _ ⟨x, hx, rfl⟩ hle
      rw [← map_rightConjugate] at hle ⊢
      have h1 : rightConjugate T x ≤ S ⊔ M := by
        intro y hy
        exact mk_mem_map_iff.mp (hle (Subgroup.mem_map_of_mem π hy))
      have h2 := c.conj_le_sup_of_le hMn hMG hWM hx h1
      have h3 : (rightConjugate T x).map π ≤ T.map π := by
        calc (rightConjugate T x).map π ≤ (T ⊔ M).map π := Subgroup.map_mono h2
          _ = T.map π := by rw [Subgroup.map_sup, hMb, sup_bot_eq]
      refine Subgroup.eq_of_le_of_card_ge h3 ?_
      rw [card_map_eq_of_ker π (hinjT x), card_map_eq_of_ker π hinjT₀, rightConjugate_card]
  obtain ⟨K, -, hKG, hKn, hGTK, hodd, hsq⟩ := exists_odd_ext hGn hMn hMG h42
  have hCn : (Subgroup.centralizer (M : Set X)).Normal := inferInstance
  have hKC : K ⊓ Subgroup.centralizer (M : Set X) = ⊥ := by
    set P := K ⊓ Subgroup.centralizer (M : Set X) with hPdef
    have hPn : P.Normal := Subgroup.normal_inf_normal _ _
    have hPodd : Odd (Nat.card P) := by
      have h1 := hodd P inf_le_left
      have hMP : M ⊓ P = ⊥ := by
        rw [eq_bot_iff, ← hcen]
        exact inf_le_inf_left M inf_le_right
      rw [← Subgroup.inf_relIndex_right, hMP, Subgroup.relIndex_bot_left] at h1
      exact Nat.not_even_iff_odd.mp fun h => h1 (even_iff_two_dvd.mp h)
    have hle := le_map_oddCore (inf_le_left.trans hKG)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) hPodd
    rwa [hO, Subgroup.map_bot, le_bot_iff] at hle
  have hAK : ∀ a ∈ A, ∀ k ∈ K, a * k = k * a := by
    intro a ha k hk
    have hmem : a⁻¹ * k⁻¹ * a * k ∈ K ⊓ Subgroup.centralizer (M : Set X) := by
      refine ⟨K.mul_mem ?_ hk, ?_⟩
      · have := hKn.conj_mem k⁻¹ (K.inv_mem hk) a⁻¹
        simpa using this
      · have h1 := hCn.conj_mem a (hAC ha) k⁻¹
        have h2 : a⁻¹ * k⁻¹ * a * k = a⁻¹ * (k⁻¹ * a * k⁻¹⁻¹) := by group
        rw [h2]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hAC ha)) h1
    rw [hKC, Subgroup.mem_bot] at hmem
    have h3 : k⁻¹ * a * k = a := by
      calc k⁻¹ * a * k = a * (a⁻¹ * k⁻¹ * a * k) := by group
        _ = a := by rw [hmem, mul_one]
    calc a * k = k * (k⁻¹ * a * k) := by group
      _ = k * a := by rw [h3]
  have hTK : ∀ t ∈ T, ∀ k ∈ K, Commute (π t) (π k) := by
    intro t ht k hk
    have htm : t ∈ (A : Set X) * (M : Set X) := by
      rw [← Subgroup.mul_normal]
      exact hTA ht
    obtain ⟨a, ha, m, hm, rfl⟩ := Set.mem_mul.mp htm
    have hm1 : π m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    show π (a * m) * π k = π k * π (a * m)
    rw [map_mul, hm1, mul_one, ← map_mul, ← map_mul, hAK a ha k hk]
  rw [Subgroup.commutator_le]
  intro x hx t ht
  have hk : ⁅x, t⁆ ∈ K := hGTK (Subgroup.commutator_mem_commutator hx ht)
  obtain ⟨e, he⟩ := c.frame.isPGroup ⟨t, ht⟩
  have hte : t ^ (2 ^ e) = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  apply hsq _ hk e
  apply (QuotientGroup.eq_one_iff _).mp
  show π (⁅x, t⁆ ^ (2 ^ e)) = 1
  have hconj : (⁅x, t⁆ * t) ^ (2 ^ e) = 1 := by
    have : ⁅x, t⁆ * t = x * t * x⁻¹ := by rw [commutatorElement_def]; group
    rw [this, conj_pow, hte, mul_one, mul_inv_cancel]
  have h1 := congrArg π hconj
  rw [map_pow, map_mul, ((hTK t ht _ hk).symm).mul_pow, ← map_pow π t, hte, map_one,
    mul_one] at h1
  rw [map_pow]
  exact h1

theorem not_le_centralizer_normalClosure (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False) :
    ¬ Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) ≤
      Subgroup.centralizer
        (Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hab
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  set M := Subgroup.normalClosure (Z₁ : Set X) with hMdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  have hMab : IsMulCommutative M :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp (hab b.2) a a.2)⟩⟩
  have hZsq : ∀ z ∈ Z₁, z ^ 2 = 1 := fun z hz =>
    ((mem_omegaOne_iff (isMulCommutative_of_le inf_le_left c.isMulCommutative_W)).mp hz).2
  have hMO : M ≤ omegaOne M := by
    change Subgroup.closure (Group.conjugatesOfSet (Z₁ : Set X)) ≤ _
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨a, ha, hay⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨d, rfl⟩ := isConj_iff.1 hay
    refine mem_omegaOne (hMn.conj_mem a (Subgroup.subset_normalClosure ha) d) ?_
    rw [conj_pow, hZsq a ha, mul_one, mul_inv_cancel]
  have hM2 : IsPGroup 2 M := fun m =>
    ⟨1, Subtype.ext (by simpa using ((mem_omegaOne_iff hMab).mp (hMO m.2)).2)⟩
  have hMG : M ≤ G := Subgroup.normalClosure_le_normal
    (SetLike.coe_subset_coe.mpr ((omegaOne_le _).trans inf_le_right))
  have hMN : ∀ x : X, x ∈ Subgroup.normalizer (M : Set X) := fun x => by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x
  have hMS : M ≤ S := le_of_isSylowOf_of_le_normalizer c.sylowFrame.sylow hM2
    (hMG.trans le_sup_left) (fun x _ => hMN x)
  exact hnn M Subgroup.le_normalClosure (le_inf hMS hMG) (fun x _ => hMN x)

theorem bender_of_lt (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    (hlt : Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) < G) :
    Bender46 G T S := by
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  set M := Subgroup.normalClosure (Z₁ : Set X) with hMdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hMN : ∀ x : X, x ∈ Subgroup.normalizer (M : Set X) := fun x => by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x
  have hTM : T ≤ Subgroup.normalizer (M : Set X) := fun t _ => hMN t
  have hCn : (Subgroup.centralizer (M : Set X)).Normal := inferInstance
  have hcard := card_sup_lt c.frame hlt hTM
  rcases c.sub_normal htop hO IH hnn hMn hlt.le hcard with hc | ⟨y, -, S₁, hB, -, hZB, -, hMB⟩
  ·
    exfalso
    apply c.not_le_centralizer_normalClosure htop hnn
    have hTC : T ≤ Subgroup.centralizer (M : Set X) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hc
    have hTgC : rightConjugate T g ≤ Subgroup.centralizer (M : Set X) := by
      have h1 := rightConjugate_le_rightConjugate hTC g
      rwa [(rightConjugate_eq_self_iff (Subgroup.centralizer (M : Set X)) g).mpr
        (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top g)] at h1
    have hZC : Z₁ ≤ Subgroup.centralizer (M : Set X) :=
      (omegaOne_le _).trans (inf_le_left.trans (sup_le hTC hTgC))
    exact Subgroup.normalClosure_le_normal (SetLike.coe_subset_coe.mpr hZC)
  · have hBM : ⁅T, M⁆ = M := le_antisymm (commutator_le_of_le_normalizer hTM) hMB
    obtain ⟨n, hcc, hAB, hAcomm, hAel, hAcard, hBen, hTel, hTcard, -, hTA⟩ := hB
    rw [hBM] at hcc hAB hAcomm hBen hZB
    have hAC : pCoreOf 2 (conjugateClosure M T) ≤ Subgroup.centralizer (M : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAcomm
    have hTA' : T ≤ pCoreOf 2 (conjugateClosure M T) ⊔ M := by
      rw [← hcc]
      exact FourEight.le_conjugateClosure M T
    have hcen : M ⊓ Subgroup.centralizer (M : Set X) = ⊥ := by
      have hs : IsSimpleGroup M := hBen.isSimpleGroup
      have hn : ((M ⊓ Subgroup.centralizer (M : Set X)).subgroupOf M).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer fun x _ =>
          Subgroup.inf_normalizer_le_normalizer_inf
            ⟨hMN x, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x⟩
      rcases hn.eq_bot_or_eq_top with hbot | htop'
      · rw [Subgroup.subgroupOf_eq_bot] at hbot
        have h1 := disjoint_iff.mp hbot
        rwa [inf_eq_left.mpr (inf_le_left : M ⊓ Subgroup.centralizer (M : Set X) ≤ M)] at h1
      · exfalso
        rw [Subgroup.subgroupOf_eq_top] at htop'
        exact c.not_le_centralizer_normalClosure htop hnn (htop'.trans inf_le_right)
    have hTG := c.commutator_le_of_inner htop hO hMn hlt.le hZB hcen hAC hTA'
    have hTGM : ⁅T, G⁆ = M := by
      apply le_antisymm
      · rw [Subgroup.commutator_comm]
        exact hTG
      · calc M = ⁅T, M⁆ := hBM.symm
          _ ≤ ⁅T, G⁆ := Subgroup.commutator_mono le_rfl hlt.le
    have hccG : conjugateClosure G T = conjugateClosure M T := by
      rw [FourEight.conjugateClosure_eq, FourEight.conjugateClosure_eq, hTGM, hBM]
    unfold Bender46
    rw [hccG, hTGM]
    refine ⟨n, hcc, hAB, hAcomm, hAel, hAcard, hBen, hTel, hTcard, ?_, hTA⟩
    rw [c.weakClosure]
    exact hZB

end Conf46

end CFSG.ComponentClassification.AschbacherTheorem3
