module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixBasic

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem eq_of_central_sylow {C Z : Subgroup X} (hZC : Z ≤ C)
    (hcent : C ≤ Subgroup.centralizer (Z : Set X)) (hZ2 : IsPGroup 2 Z)
    (hodd : ¬ 2 ∣ Z.relIndex C) (hO : CFSG.oddCore C = ⊥) : Z = C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₀ : Subgroup C := Z.subgroupOf C
  have hP₀2 : IsPGroup 2 P₀ := hZ2.comap_subtype
  have hP₀idx : ¬ 2 ∣ P₀.index := hodd
  set P : Sylow 2 C := hP₀2.toSylow hP₀idx
  have hPeq : (P : Subgroup C) = P₀ := IsPGroup.toSylow_coe hP₀2 hP₀idx
  have hcentP : Subgroup.normalizer ((P : Subgroup C) : Set C) ≤
      Subgroup.centralizer ((P : Subgroup C) : Set C) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    rw [hPeq] at hp
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent x.2) p hp)
  set N := (MonoidHom.transferSylow P hcentP).ker
  have hNodd : Odd (Nat.card N) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    (MonoidHom.not_dvd_card_ker_transferSylow P hcentP))
  have hNle : N ≤ CFSG.oddCore C := le_sSup ⟨inferInstance, hNodd⟩
  rw [hO, le_bot_iff] at hNle
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hcentP
  change Subgroup.IsComplement' N (P : Subgroup C) at hcomp
  rw [hNle, Subgroup.isComplement'_bot_left, hPeq] at hcomp
  apply le_antisymm hZC
  intro x hx
  have : (⟨x, hx⟩ : C) ∈ P₀ := hcomp ▸ Subgroup.mem_top _
  exact this

theorem oddCore_eq_bot_of_le {C G : Subgroup X} (hCG : C ≤ G)
    (hN : G ≤ Subgroup.normalizer (C : Set X)) (hO : CFSG.oddCore G = ⊥) :
    CFSG.oddCore C = ⊥ := by
  have : (CFSG.oddCore C).Characteristic := OddCore.characteristic C
  have hle : (CFSG.oddCore C).map C.subtype ≤ (CFSG.oddCore G).map G.subtype :=
    le_map_oddCore ((Subgroup.map_subtype_le _).trans hCG)
      (fun x hx => mem_normalizer_map_of_characteristic (CFSG.oddCore C) (hN hx))
      (by rw [Subgroup.card_map_of_injective C.subtype_injective]; exact odd_card_oddCore C)
  rw [hO, Subgroup.map_bot, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp hle

omit [Finite X] in
theorem commutator_mem_of_frame {G T : Subgroup X} (hF : Frame G T) (htop : G ⊔ T = ⊤)
    (hT : IsMulCommutative T) (a b : X) : a * b * a⁻¹ * b⁻¹ ∈ G := by
  have : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer hF.le_normalizer
  obtain ⟨t₁, ht₁, h₁, hh₁, rfl⟩ := hF.mem_sup_iff.mp (htop ▸ Subgroup.mem_top a)
  obtain ⟨t₂, ht₂, h₂, hh₂, rfl⟩ := hF.mem_sup_iff.mp (htop ▸ Subgroup.mem_top b)
  rw [← QuotientGroup.eq_one_iff]
  have hπ₁ : ((h₁ : X) : X ⧸ G) = 1 := (QuotientGroup.eq_one_iff _).mpr hh₁
  have hπ₂ : ((h₂ : X) : X ⧸ G) = 1 := (QuotientGroup.eq_one_iff _).mpr hh₂
  have hcomm : t₁ * t₂ = t₂ * t₁ :=
    congrArg Subtype.val (hT.is_comm.comm ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩)
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hπ₁, hπ₂, mul_one]
  rw [← QuotientGroup.mk_mul, hcomm, QuotientGroup.mk_mul]
  group

namespace Conf46

variable {G T S Q H : Subgroup X} {g : X}

theorem le_normalizer_omegaOne_of_forall (c : Conf46 G T S Q H g)
    (h : ∀ y ∈ G, rightConjugate (omegaOne T) y ≤ S) :
    G ≤ Subgroup.normalizer ((omegaOne (T ⊔ rightConjugate T g) : Subgroup X) : Set X) := by
  have hmem : ∀ y ∈ G, rightConjugate (omegaOne T) y ≤ omegaOne (T ⊔ rightConjugate T g) :=
    fun y hy => by
      rw [← c.weakClosure_omegaOne]
      exact rightConjugate_le_relativeWeakClosure hy (h y hy)
  intro y hy
  rw [← rightConjugate_eq_self_iff]
  apply Subgroup.eq_of_le_of_card_ge _ (by rw [rightConjugate_card])
  have hVeq := c.omegaOne_W_eq_conj
  have hsup : rightConjugate (omegaOne T ⊔ rightConjugate (omegaOne T) g) y =
      rightConjugate (omegaOne T) y ⊔ rightConjugate (omegaOne T) (g * y) := by
    rw [← rightConjugate_mul]
    exact Subgroup.map_sup _ _ _
  calc rightConjugate (omegaOne (T ⊔ rightConjugate T g)) y
      = rightConjugate (omegaOne T ⊔ rightConjugate (omegaOne T) g) y := by rw [hVeq]
    _ = rightConjugate (omegaOne T) y ⊔ rightConjugate (omegaOne T) (g * y) := hsup
    _ ≤ omegaOne (T ⊔ rightConjugate T g) :=
        sup_le (hmem y hy) (hmem _ (G.mul_mem c.mem hy))

theorem exists_odd_extension (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) {N : Subgroup X}
    (hNn : N.Normal) (hNG : N ≤ G) (hNS : N ≤ S)
    (hZN : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ N) :
    ∃ K : Subgroup X, N ≤ K ∧ K ≤ G ∧ K.Normal ∧ ⁅G, omegaOne T⁆ ≤ K ∧
      (∀ C ≤ K, ¬ 2 ∣ N.relIndex C) ∧ (∀ k ∈ K, k ^ 2 ∈ N → k ∈ N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := T ⊔ rightConjugate T g with hWdef
  set Z₁ := omegaOne (W ⊓ G) with hZ₁def
  set U := omegaOne T with hUdef
  set V := omegaOne W with hVdef
  have hUT : U ≤ T := omegaOne_le T
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  have hWU : relativeWeakClosure G U S = V := c.weakClosure_omegaOne
  have hVeq : V = U ⊔ Z₁ := c.omegaOne_W
  set π := QuotientGroup.mk' N with hπ
  have hkerπ : π.ker = N := QuotientGroup.ker_mk' N
  have hinjU : ∀ x : X, ∀ y ∈ rightConjugate U x, π y = 1 → y = 1 := by
    intro x y hy h1
    have hyN : y ∈ N := (QuotientGroup.eq_one_iff y).mp h1
    have hyT : y ∈ rightConjugate T x ⊓ rightConjugate G x := by
      refine ⟨rightConjugate_le_rightConjugate hUT x hy, ?_⟩
      have hxN : x ∈ Subgroup.normalizer (G : Set X) := by
        rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x
      rw [(rightConjugate_eq_self_iff _ x).mpr hxN]
      exact hNG hyN
    rw [← rightConjugate_inf, c.frame.inf_eq_bot, rightConjugate_bot] at hyT
    exact hyT
  have hinjU₀ : ∀ y ∈ U, π y = 1 → y = 1 := fun y hy h1 =>
    hinjU 1 y (by rw [rightConjugate_one]; exact hy) h1
  have hFU : Frame G U := ⟨hUT.trans c.frame.le_normalizer,
    by rw [eq_bot_iff, ← c.frame.inf_eq_bot]; exact inf_le_inf_right G hUT,
    c.frame.isPGroup.to_le hUT⟩
  have hGUn : (G ⊔ U).Normal := ⟨fun n hn x => by
    have h := commutator_mem_of_frame c.frame htop c.isMulCommutative x n
    have : x * n * x⁻¹ = (x * n * x⁻¹ * n⁻¹) * n := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h) hn⟩
  have hSU : IsSylowOf 2 (S ⊓ (G ⊔ U)) (G ⊔ U) :=
    c.sylowFrame.sylow.inf_of_le_normalizer (sup_le_sup_left hUT G)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hZ₁b : Z₁.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hkerπ]
    exact hZN
  have h42 : Hyp42 (G.map π) (U.map π) ((S ⊓ (G ⊔ U)).map π) := by
    refine ⟨hFU.map N hNG, ?_, Subgroup.map_mono (le_inf (hUT.trans c.le_S) le_sup_right),
      ?_⟩
    · rw [← Subgroup.map_sup]
      exact IsSylowOf.map hSU π
    · rintro _ ⟨x, hx, rfl⟩ hle
      rw [← map_rightConjugate] at hle ⊢
      have h1 : rightConjugate U x ≤ S := by
        intro y hy
        have hy' : π y ∈ (S ⊓ (G ⊔ U)).map π := hle (Subgroup.mem_map_of_mem π hy)
        exact (sup_le inf_le_left hNS) (mk_mem_map_iff.mp hy')
      have h2 : rightConjugate U x ≤ V := by
        rw [← hWU]
        exact rightConjugate_le_relativeWeakClosure hx h1
      have h3 : (rightConjugate U x).map π ≤ U.map π := by
        calc (rightConjugate U x).map π ≤ V.map π := Subgroup.map_mono h2
          _ = U.map π := by rw [hVeq, Subgroup.map_sup, hZ₁b, sup_bot_eq]
      refine Subgroup.eq_of_le_of_card_ge h3 ?_
      rw [card_map_eq_of_ker π (hinjU x), card_map_eq_of_ker π hinjU₀, rightConjugate_card]
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
  · intro k hk hk2
    have hπk : π k ^ (2 ^ 1) = 1 := by
      rw [pow_one, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hk2
    exact (QuotientGroup.eq_one_iff k).mp
      (eq_one_of_two_pow_of_odd (show π k ∈ Kb from hk) hKbodd hπk)

theorem normalizer_omegaOne_of_central (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (hO : CFSG.oddCore G = ⊥) {N : Subgroup X} (hNn : N.Normal) (hNG : N ≤ G) (hNS : N ≤ S)
    (hZN : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ N)
    (hUN : omegaOne T ≤ Subgroup.centralizer (N : Set X)) :
    G ≤ Subgroup.normalizer ((omegaOne (T ⊔ rightConjugate T g) : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := omegaOne T with hUdef
  have hUT : U ≤ T := omegaOne_le T
  obtain ⟨K, hNK, hKG, hKn, hcomm, hodd, hsq⟩ := c.exists_odd_extension htop hNn hNG hNS hZN
  set C := K ⊓ Subgroup.centralizer (N : Set X) with hCdef
  have hCN : C ≤ N := by
    have hCn : C.Normal := by
      have : (Subgroup.centralizer (N : Set X)).Normal := inferInstance
      exact Subgroup.normal_inf_normal _ _
    have heq : N ⊓ C = C := by
      apply eq_of_central_sylow inf_le_right
        ((inf_le_right : C ≤ _).trans (Subgroup.centralizer_le
          (SetLike.coe_subset_coe.mpr inf_le_left)))
        (c.isPGroup_S.to_le (inf_le_left.trans hNS))
      · rw [Subgroup.inf_relIndex_right]
        exact hodd C inf_le_left
      · exact oddCore_eq_bot_of_le (inf_le_left.trans hKG)
          (by rw [Subgroup.normalizer_eq_top]; exact le_top) hO
    rw [← heq]
    exact inf_le_left
  have hUNc : ⁅U, N⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUN
  have h3 : ⁅⁅K, U⁆, N⁆ = ⊥ := by
    apply Subgroup.commutator_commutator_eq_bot_of_rotate
    · rw [hUNc, Subgroup.commutator_bot_left]
    · rw [eq_bot_iff]
      calc ⁅⁅N, K⁆, U⁆ ≤ ⁅N, U⁆ :=
            Subgroup.commutator_mono (Subgroup.commutator_le_left N K) le_rfl
        _ = ⊥ := by rw [Subgroup.commutator_comm, hUNc]
  have hKU : ⁅K, U⁆ ≤ N :=
    (le_inf (Subgroup.commutator_le_left K U)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)).trans hCN
  have hxu : ∀ x ∈ G, ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ N := by
    intro x hx u hu
    have hu2 : u ^ 2 = 1 := ((mem_omegaOne_iff c.isMulCommutative).mp hu).2
    set k := x * u * x⁻¹ * u⁻¹ with hk
    have hkK : k ∈ K := hcomm (Subgroup.commutator_mem_commutator hx hu)
    have huinv : u⁻¹ = u := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, hu2]
    have hconj : u * k * u⁻¹ = k⁻¹ := by
      rw [hk, huinv]
      calc u * (x * u * x⁻¹ * u) * u = u * x * u * x⁻¹ * (u * u) := by group
        _ = u * x * u * x⁻¹ := by rw [← pow_two, hu2, mul_one]
        _ = (x * u * x⁻¹ * u)⁻¹ := by
          rw [show (x * u * x⁻¹ * u)⁻¹ = u⁻¹ * x * u⁻¹ * x⁻¹ by group, huinv]
    have hk2 : k ^ 2 ∈ N := by
      have hmem : k * u * k⁻¹ * u⁻¹ ∈ N :=
        hKU (Subgroup.commutator_mem_commutator hkK hu)
      have h' : u * k⁻¹ * u⁻¹ = k := by
        calc u * k⁻¹ * u⁻¹ = (u * k * u⁻¹)⁻¹ := by group
          _ = k := by rw [hconj, inv_inv]
      have heq : k * u * k⁻¹ * u⁻¹ = k ^ 2 := by
        calc k * u * k⁻¹ * u⁻¹ = k * (u * k⁻¹ * u⁻¹) := by group
          _ = k ^ 2 := by rw [h', pow_two]
      rwa [heq] at hmem
    exact hsq k hkK hk2
  apply c.le_normalizer_omegaOne_of_forall
  intro y hy w hw
  rw [mem_rightConjugate_iff] at hw
  have h1 := hxu y⁻¹ (G.inv_mem hy) _ hw
  have hw' : w = (y⁻¹ * (y * w * y⁻¹) * y⁻¹⁻¹ * (y * w * y⁻¹)⁻¹) * (y * w * y⁻¹) := by group
  rw [hw']
  exact S.mul_mem (hNS h1) (c.le_S (hUT hw))

theorem omegaOne_W_normal (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (hO : CFSG.oddCore G = ⊥)
    (hZ : G ≤ Subgroup.normalizer
      ((omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Subgroup X) : Set X)) :
    G ≤ Subgroup.normalizer ((omegaOne (T ⊔ rightConjugate T g) : Subgroup X) : Set X) := by
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  have hWab := c.isMulCommutative_W
  have hZ₁W : Z₁ ≤ T ⊔ rightConjugate T g := (omegaOne_le _).trans inf_le_left
  have hTZ₁ : T ≤ Subgroup.centralizer (Z₁ : Set X) := fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      congrArg Subtype.val (hWab.is_comm.comm ⟨z, hZ₁W hz⟩ ⟨t, Subgroup.mem_sup_left ht⟩)
  have hZ₁n : Z₁.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le hZ (hTZ₁.trans (Subgroup.centralizer_le_normalizer _))
  exact c.normalizer_omegaOne_of_central htop hO hZ₁n ((omegaOne_le _).trans inf_le_right)
    (hZ₁W.trans c.W_le_S) le_rfl ((omegaOne_le T).trans hTZ₁)

end Conf46

end CFSG.ComponentClassification.AschbacherTheorem3
