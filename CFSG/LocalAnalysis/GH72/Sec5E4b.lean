module

public import CFSG.LocalAnalysis.GH72.Sec5DBasic

public section

namespace CFSG.GH72

open Subgroup

namespace E4b

open G5d

section Four

variable {G : Type*} [Group G]

theorem exists_ne_one_ne_of_card_eq_four {L : Type*} [Group L] (hL : Nat.card L = 4) (x : L) :
    ∃ y : L, y ≠ 1 ∧ y ≠ x := by
  by_contra h
  push Not at h
  have hsurj : Function.Surjective fun b : Bool => if b then x else (1 : L) := by
    intro y
    by_cases hy : y = 1
    · exact ⟨false, by simp [hy]⟩
    · exact ⟨true, by simp [h y hy]⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [hL, Nat.card_eq_fintype_card, Fintype.card_bool] at this
  omega

theorem exists_mem_ne_one_ne {K : Subgroup G} (hK : IsKleinFour K) (x : G) :
    ∃ y ∈ K, y ≠ 1 ∧ y ≠ x := by
  by_cases hx : x ∈ K
  · obtain ⟨y, hy1, hyx⟩ := exists_ne_one_ne_of_card_eq_four (@IsKleinFour.card_four _ _ hK)
      (⟨x, hx⟩ : K)
    exact ⟨y, y.2, fun h => hy1 (Subtype.ext h), fun h => hyx (Subtype.ext h)⟩
  · obtain ⟨y, hy1, -⟩ := exists_ne_one_ne_of_card_eq_four (@IsKleinFour.card_four _ _ hK) 1
    exact ⟨y, y.2, fun h => hy1 (Subtype.ext h), fun h => hx (h ▸ y.2)⟩

theorem C_inf_C_le_centralizer {K : Subgroup G} (hK : IsKleinFour K) {x x' : G} (hx : x ∈ K)
    (hx1 : x ≠ 1) (hx' : x' ∈ K) (hx'1 : x' ≠ 1) (hxx' : x ≠ x') :
    C x ⊓ C x' ≤ centralizer (K : Set G) := by
  intro d hd
  obtain ⟨hdx, hdx'⟩ := mem_inf.mp hd
  rw [mem_centralizer_singleton_iff] at hdx hdx'
  rw [mem_centralizer_iff]
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1, one_mul, mul_one]
  by_cases hzx : z = x
  · rw [hzx]
    exact hdx.symm
  by_cases hzx' : z = x'
  · rw [hzx']
    exact hdx'.symm
  have hzK : (⟨z, hz⟩ : K) = ⟨x, hx⟩ * ⟨x', hx'⟩ :=
    @IsKleinFour.eq_mul_of_ne_all _ _ hK _ _ _ (fun h => hx1 (congrArg Subtype.val h))
      (fun h => hx'1 (congrArg Subtype.val h)) (fun h => hxx' (congrArg Subtype.val h))
      (fun h => hz1 (congrArg Subtype.val h)) (fun h => hzx (congrArg Subtype.val h))
      (fun h => hzx' (congrArg Subtype.val h))
  rw [show z = x * x' from congrArg Subtype.val hzK]
  exact (Commute.mul_right (show Commute d x from hdx) (show Commute d x' from hdx')).symm

end Four

section FourQuot

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_sup_of_quotIs_kleinFour {K N T : Subgroup G}
    (hq : QuotIs K N fun L _ => IsKleinFour L) (hN : Odd (Nat.card N)) (hTK : T ≤ K)
    (hT : Nat.card T = 4) : K ≤ T ⊔ N := by
  obtain ⟨L, _, f, -, hker, hL⟩ := hq
  have hL4 : Nat.card L = 4 := @IsKleinFour.card_four _ _ hL
  have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL4]; norm_num)
  let g : T →* L := f.comp (inclusion hTK)
  have hTN : T ⊓ N = ⊥ := inf_eq_bot_of_coprime (by
    rw [hT, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hN))
  have hinj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    have h1 : inclusion hTK t ∈ f.ker := ht
    rw [hker, mem_subgroupOf] at h1
    have h2 : (t : G) ∈ T ⊓ N := ⟨t.2, h1⟩
    rw [hTN, mem_bot] at h2
    exact mem_bot.mpr (Subtype.ext h2)
  have hsurj : Function.Surjective g :=
    ((Nat.bijective_iff_injective_and_card g).mpr ⟨hinj, by rw [hT, hL4]⟩).2
  intro k hk
  obtain ⟨t, ht⟩ := hsurj (f ⟨k, hk⟩)
  have hmem : (inclusion hTK t)⁻¹ * ⟨k, hk⟩ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (g t)⁻¹ * f ⟨k, hk⟩ = 1
    rw [ht, inv_mul_cancel]
  rw [hker, mem_subgroupOf] at hmem
  have hk' : k = (t : G) * ((t : G)⁻¹ * k) := by group
  rw [hk']
  exact mul_mem_sup t.2 hmem

end FourQuot

theorem xySup_le_of {G : Type*} [Group G] {X Y K : Subgroup G} {f : G → G → Subgroup G}
    (h : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → f x y ≤ K) : xySup X Y f ≤ K :=
  iSup_le fun x => iSup_le fun hx => iSup_le fun hx1 => iSup_le fun y => iSup_le fun hy =>
    iSup_le fun hy1 => h x hx hx1 y hy hy1

section Orientation

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem covers_normalizer_of_isSylowOf_O (hp : p.Prime) {A Z M M₀ H Q : Subgroup G}
    (hA2 : IsPGroup 2 A) (hZA : Z ≤ A) (hM : M = centralizer (Z : Set G)) (hM₀M : M₀ ≤ M)
    (hOM₀ : O M ≤ M₀)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ → Covers H M₀ (O M) → ∀ z ∈ Z, z ≠ 1 → z ∈ H →
      O H ⊓ C z ≤ O (C z))
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1) (hH : H ≠ ⊤) (hAH : A ≤ H) (hcov : Covers H M₀ (O M))
    (hQ : ABGLocalTools.IsSylowOf p Q (O H)) (hAQ : A ≤ normalizer (Q : Set G)) :
    Covers (normalizer (Q : Set G)) M₀ (O M) := by
  have : Fact p.Prime := ⟨hp⟩
  have hZH : Z ≤ H := hZA.trans hAH
  have hZN : Z ≤ normalizer ((H ⊓ normalizer (Q : Set G) : Subgroup G) : Set G) :=
    fun w hw => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer (hZH hw), le_normalizer (hAQ (hZA hw))⟩
  have hMz : M ≤ C z := by
    rw [hM]
    exact centralizer_le (Set.singleton_subset_iff.mpr hzZ)
  have hOHM : O H ⊓ M ≤ O M := by
    have h1 : O H ⊓ M ≤ O (C z) :=
      (le_inf inf_le_left (inf_le_right.trans hMz)).trans (h413 H hH hcov z hzZ hz1 (hZH hzZ))
    exact (le_inf h1 inf_le_right).trans (O_inf_le_O_of_le hMz)
  have h := covers_of_eq_O_sup (hA2.to_le hZA) hZH hZN inf_le_left
    (eq_sup_inf_normalizer_of_isSylowOf (map_subtype_le _) (le_normalizer_O _) hQ) hM hM₀M hOM₀
    hOHM hcov
  unfold Covers at h ⊢
  exact h.trans (sup_le_sup_right (inf_le_inf_right _ inf_le_right) _)

theorem exists_K {A M₀ OM P : Subgroup G}
    (hM₀n : normalizer (A : Set G) ≤ normalizer (M₀ : Set G))
    (hOMn : normalizer (A : Set G) ≤ normalizer (OM : Set G))
    (h46 : ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ → IsMaxInvIn p A ⊤ P₂ →
      ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (hK : ∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K M₀ OM) (hP : IsMaxInvIn p A ⊤ P) :
    ∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K M₀ OM ∧ IsMaxInvIn p A K (P ⊓ K) ∧
      (∀ K' T : Subgroup G, CFSG.IsPLocal p K' → A ≤ K' → Covers K' M₀ OM →
        T ≤ K' → IsPGroup p T → A ≤ normalizer (T : Set G) →
        Nat.card T ≤ Nat.card (P ⊓ K : Subgroup G)) ∧
      (∀ K' : Subgroup G, CFSG.IsPLocal p K' → A ≤ K' → Covers K' M₀ OM →
        P ⊓ K ≤ K' →
        Nat.card (P ⊓ K ⊓ O K' : Subgroup G) ≤ Nat.card (P ⊓ K ⊓ O K : Subgroup G)) := by
  set 𝒞 : Set (Subgroup G × Subgroup G) := {KT | CFSG.IsPLocal p KT.1 ∧ A ≤ KT.1 ∧
    Covers KT.1 M₀ OM ∧ KT.2 ≤ KT.1 ∧ IsPGroup p KT.2 ∧
    A ≤ normalizer (KT.2 : Set G)}
  have hne : 𝒞.Nonempty := by
    obtain ⟨K, hK, hAK, hcov⟩ := hK
    refine ⟨(K, ⊥), hK, hAK, hcov, bot_le, IsPGroup.of_bot, ?_⟩
    show A ≤ normalizer ((⊥ : Subgroup G) : Set G)
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨⟨K₁, T₁⟩, h₁, hmax₁⟩ :=
    Set.exists_max_image 𝒞 (fun KT => Nat.card KT.2) (Set.toFinite 𝒞) hne
  have hle₁ : ∀ K' T' : Subgroup G, CFSG.IsPLocal p K' → A ≤ K' →
      Covers K' M₀ OM → T' ≤ K' → IsPGroup p T' →
      A ≤ normalizer (T' : Set G) → Nat.card T' ≤ Nat.card T₁ :=
    fun K' T' h1 h2 h3 h4 h5 h6 => hmax₁ (K', T') ⟨h1, h2, h3, h4, h5, h6⟩
  set 𝒞' : Set (Subgroup G × Subgroup G) := {KT | KT ∈ 𝒞 ∧ Nat.card KT.2 = Nat.card T₁}
  obtain ⟨⟨K₂, T₂⟩, hmem₂, hmax₂⟩ :=
    Set.exists_max_image 𝒞' (fun KT => Nat.card (KT.2 ⊓ O KT.1 : Subgroup G))
      (Set.toFinite 𝒞') ⟨(K₁, T₁), h₁, rfl⟩
  obtain ⟨⟨hK₂, hAK₂, hcov₂, hTK₂, hT₂p, hAT₂⟩, hT₂⟩ : (CFSG.IsPLocal p K₂ ∧ A ≤ K₂ ∧
      Covers K₂ M₀ OM ∧ T₂ ≤ K₂ ∧ IsPGroup p T₂ ∧
      A ≤ normalizer (T₂ : Set G)) ∧ Nat.card T₂ = Nat.card T₁ := hmem₂
  obtain ⟨P₁, hP₁, hTP₁⟩ := exists_isMaxInvIn_ge (H := ⊤) le_top hT₂p hAT₂
  obtain ⟨g, hg, hgP⟩ := h46 P₁ P hP₁ hP
  have hAc : A.map (MulAut.conj g).toMonoidHom = A := G4b.mem_normalizer_iff_map_conj_eq'.mp hg
  have hcov₃ := covers_map_conj hcov₂ g
  rw [G4b.mem_normalizer_iff_map_conj_eq'.mp (hM₀n hg),
    G4b.mem_normalizer_iff_map_conj_eq'.mp (hOMn hg)] at hcov₃
  have hnc : ∀ R : Subgroup G, (normalizer (R : Set G)).map (MulAut.conj g).toMonoidHom =
      normalizer ((R.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
    fun R => map_equiv_normalizer_eq R (MulAut.conj g)
  have hOc : (O K₂).map (MulAut.conj g).toMonoidHom = O (K₂.map (MulAut.conj g).toMonoidHom) :=
    G4b.map_O (MulAut.conj g) K₂
  have hcinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  generalize (MulAut.conj g).toMonoidHom = c at hAc hcov₃ hnc hOc hcinj hgP
  have hKloc : CFSG.IsPLocal p (K₂.map c) := by
    obtain ⟨R, hR1, hRp, hK₂R⟩ := hK₂
    refine ⟨R.map c, fun h => hR1 ((map_eq_bot_iff_of_injective R hcinj).mp h), hRp.map c, ?_⟩
    rw [hK₂R, hnc]
  have hAK : A ≤ K₂.map c := by
    rw [← hAc]
    exact map_mono hAK₂
  have hTK : T₂.map c ≤ K₂.map c := map_mono hTK₂
  have hTp : IsPGroup p (T₂.map c) := hT₂p.map c
  have hAT : A ≤ normalizer ((T₂.map c : Subgroup G) : Set G) := by
    rw [← hnc, ← hAc]
    exact map_mono hAT₂
  have hcardT : Nat.card (T₂.map c) = Nat.card T₁ := by
    rw [card_map_of_injective hcinj, hT₂]
  have hPK : P ⊓ K₂.map c = T₂.map c := by
    refine (eq_of_le_of_card_ge (le_inf (hgP ▸ map_mono hTP₁) hTK) ?_).symm
    rw [hcardT]
    exact hle₁ _ _ hKloc hAK hcov₃ inf_le_right (hP.2.1.to_le inf_le_left) fun a ha =>
      inf_normalizer_le_normalizer_inf ⟨hP.2.2.1 ha, le_normalizer (hAK ha)⟩
  refine ⟨K₂.map c, hKloc, hAK, hcov₃, ?_, fun K' T' h1 h2 h3 h4 h5 h6 => ?_,
    fun K' h1 h2 h3 h4 => ?_⟩
  · rw [hPK]
    refine ⟨hTK, hTp, hAT, fun Q hQK hQp hAQ hTQ => (eq_of_le_of_card_ge hTQ ?_).symm⟩
    rw [hcardT]
    exact hle₁ _ Q hKloc hAK hcov₃ hQK hQp hAQ
  · rw [hPK, hcardT]
    exact hle₁ K' T' h1 h2 h3 h4 h5 h6
  · rw [hPK] at h4 ⊢
    rw [← hOc, ← Subgroup.map_inf _ _ _ hcinj, card_map_of_injective hcinj]
    exact hmax₂ (K', T₂.map c) ⟨⟨h1, h2, h3, h4, hTp, hAT⟩, hcardT⟩

theorem exists_K_eq_normalizer (hp : p.Prime) (hp2 : p ≠ 2) {A Z M M₀ W P K : Subgroup G}
    (hA2 : IsPGroup 2 A) (hZA : Z ≤ A) (hM : M = centralizer (Z : Set G)) (hM₀M : M₀ ≤ M)
    (hOM₀ : O M ≤ M₀)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ → Covers H M₀ (O M) → ∀ z ∈ Z, z ≠ 1 → z ∈ H →
      O H ⊓ C z ≤ O (C z))
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1) (hne : ∀ H : Subgroup G, CFSG.IsPLocal p H → H ≠ ⊤)
    (hW : ∀ H : Subgroup G, CFSG.IsPLocal p H → A ≤ H → Covers H M₀ (O M) →
      ¬ Sec4Setting.PConstrainedWrt p A H W)
    (hP : IsMaxInvIn p A ⊤ P) (hK : CFSG.IsPLocal p K) (hAK : A ≤ K)
    (hcov : Covers K M₀ (O M)) (hPK : IsMaxInvIn p A K (P ⊓ K))
    (hmax₁ : ∀ K' T : Subgroup G, CFSG.IsPLocal p K' → A ≤ K' → Covers K' M₀ (O M) →
      T ≤ K' → IsPGroup p T → A ≤ normalizer (T : Set G) →
      Nat.card T ≤ Nat.card (P ⊓ K : Subgroup G))
    (hmax₂ : ∀ K' : Subgroup G, CFSG.IsPLocal p K' → A ≤ K' → Covers K' M₀ (O M) →
      P ⊓ K ≤ K' →
      Nat.card (P ⊓ K ⊓ O K' : Subgroup G) ≤ Nat.card (P ⊓ K ⊓ O K : Subgroup G)) :
    ∃ K' : Subgroup G, (CFSG.IsPLocal p K' ∧ A ≤ K' ∧ Covers K' M₀ (O M) ∧
        IsMaxInvIn p A K' (P ⊓ K') ∧ K' = normalizer ((P ⊓ K' ⊓ O K' : Subgroup G) : Set G) ∧
        W ≤ centralizer ((P ⊓ K' ⊓ O K' : Subgroup G) : Set G)) ∧
      (∀ K'' T : Subgroup G, CFSG.IsPLocal p K'' → A ≤ K'' → Covers K'' M₀ (O M) →
        T ≤ K'' → IsPGroup p T → A ≤ normalizer (T : Set G) →
        Nat.card T ≤ Nat.card (P ⊓ K' : Subgroup G)) ∧
      (∀ K'' : Subgroup G, CFSG.IsPLocal p K'' → A ≤ K'' → Covers K'' M₀ (O M) →
        P ⊓ K' ≤ K'' →
        Nat.card (P ⊓ K' ⊓ O K'' : Subgroup G) ≤ Nat.card (P ⊓ K' ⊓ O K' : Subgroup G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : ∀ R : Subgroup G, IsPGroup p R → Odd (Nat.card R) := fun R hR => by
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hVS : ABGLocalTools.IsSylowOf p (P ⊓ K ⊓ O K) (O K) :=
    isSylowOf_inf_O_of_isMaxInvIn hp hA2 (hAK.trans le_normalizer) hPK
  have hAV : A ≤ normalizer ((P ⊓ K ⊓ O K : Subgroup G) : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨hPK.2.2.1 ha, le_normalizer_O K (hAK ha)⟩
  have hV1 : P ⊓ K ⊓ O K ≠ ⊥ := by
    obtain ⟨R, hR1, hRp, hKR⟩ := hK
    have hRK : R ≤ K := by
      rw [hKR]
      exact le_normalizer
    have hRT : R ⊔ (P ⊓ K) = P ⊓ K := hPK.2.2.2 (R ⊔ (P ⊓ K)) (sup_le hRK inf_le_right)
      (IsPGroup.to_sup_of_normal_left' hRp hPK.2.1 (inf_le_right.trans hKR.le))
      (fun a ha => by
        rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
          mem_normalizer_iff_map_conj_eq.mp (hKR.le (hAK ha)),
          mem_normalizer_iff_map_conj_eq.mp (hPK.2.2.1 ha)])
      le_sup_right
    intro hbot
    apply hR1
    rw [eq_bot_iff, ← hbot]
    exact le_inf (le_sup_left.trans hRT.le) (le_O_of_le_normalizer hRK hKR.le (hodd R hRp))
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup G, K' = normalizer ((P ⊓ K ⊓ O K : Subgroup G) : Set G) :=
    ⟨_, rfl⟩
  have hK'loc : CFSG.IsPLocal p K' := ⟨_, hV1, hVS.isPGroup, hK'⟩
  have hAK' : A ≤ K' := hK' ▸ hAV
  have hcov' : Covers K' M₀ (O M) := hK' ▸ covers_normalizer_of_isSylowOf_O hp hA2 hZA hM hM₀M
    hOM₀ h413 hzZ hz1 (hne K hK) hAK hcov hVS hAV
  have hTK' : P ⊓ K ≤ K' := by
    rw [hK']
    intro t ht
    exact inf_normalizer_le_normalizer_inf ⟨le_normalizer ht, le_normalizer_O K ht.2⟩
  have hPK' : P ⊓ K' = P ⊓ K := by
    refine (eq_of_le_of_card_ge (le_inf inf_le_left hTK') ?_).symm
    exact hmax₁ K' (P ⊓ K') hK'loc hAK' hcov' inf_le_right (hP.2.1.to_le inf_le_left)
      fun a ha => inf_normalizer_le_normalizer_inf ⟨hP.2.2.1 ha, le_normalizer (hAK' ha)⟩
  have hVK' : P ⊓ K ⊓ O K' = P ⊓ K ⊓ O K := by
    have hle : P ⊓ K ⊓ O K ≤ P ⊓ K ⊓ O K' := le_inf inf_le_left (by
      rw [hK']
      exact le_O_of_le_normalizer le_normalizer le_rfl (hodd _ hVS.isPGroup))
    exact (eq_of_le_of_card_ge hle (hmax₂ K' hK'loc hAK' hcov' hTK')).symm
  have hmaxK' : IsMaxInvIn p A K' (P ⊓ K) := ⟨hTK', hPK.2.1, hPK.2.2.1,
    fun Q hQK' hQp hAQ hTQ =>
      (eq_of_le_of_card_ge hTQ (hmax₁ K' Q hK'loc hAK' hcov' hQK' hQp hAQ)).symm⟩
  refine ⟨K', ⟨hK'loc, hAK', hcov', ?_, ?_, ?_⟩, fun K'' T h1 h2 h3 h4 h5 h6 => ?_,
    fun K'' h1 h2 h3 h4 => ?_⟩
  · rw [hPK']
    exact hmaxK'
  · rw [hPK', hVK']
    exact hK'
  ·
    rw [hPK', hVK']
    by_contra hWV
    exact hW K' hK'loc hAK' hcov' ⟨P ⊓ K ⊓ O K,
      hVK' ▸ isSylowOf_inf_O_of_isMaxInvIn hp hA2 (hAK'.trans le_normalizer) hmaxK', hAV, hWV⟩
  · rw [hPK']
    exact hmax₁ K'' T h1 h2 h3 h4 h5 h6
  · rw [hPK'] at h4 ⊢
    rw [hVK']
    exact hmax₂ K'' h1 h2 h3 h4

theorem exists_K_normalizer (hp : p.Prime) (hp2 : p ≠ 2) {A Z M M₀ W P : Subgroup G}
    (hA2 : IsPGroup 2 A) (hZA : Z ≤ A) (hM : M = centralizer (Z : Set G)) (hM₀M : M₀ ≤ M)
    (hOM₀ : O M ≤ M₀) (hM₀n : normalizer (A : Set G) ≤ normalizer (M₀ : Set G))
    (hOMn : normalizer (A : Set G) ≤ normalizer (O M : Set G))
    (h46 : ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ → IsMaxInvIn p A ⊤ P₂ →
      ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ → Covers H M₀ (O M) → ∀ z ∈ Z, z ≠ 1 → z ∈ H →
      O H ⊓ C z ≤ O (C z))
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1) (hne : ∀ H : Subgroup G, CFSG.IsPLocal p H → H ≠ ⊤)
    (hW : ∀ H : Subgroup G, CFSG.IsPLocal p H → A ≤ H → Covers H M₀ (O M) →
      ¬ Sec4Setting.PConstrainedWrt p A H W)
    (hK : ∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K M₀ (O M)) (hP : IsMaxInvIn p A ⊤ P) :
    ∃ K : Subgroup G, (CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K M₀ (O M) ∧
        IsMaxInvIn p A K (P ⊓ K) ∧ K = normalizer ((P ⊓ K ⊓ O K : Subgroup G) : Set G) ∧
        W ≤ centralizer ((P ⊓ K ⊓ O K : Subgroup G) : Set G)) ∧
      (∀ K' T : Subgroup G, CFSG.IsPLocal p K' → A ≤ K' → Covers K' M₀ (O M) →
        T ≤ K' → IsPGroup p T → A ≤ normalizer (T : Set G) →
        Nat.card T ≤ Nat.card (P ⊓ K : Subgroup G)) ∧
      (∀ K' : Subgroup G, CFSG.IsPLocal p K' → A ≤ K' → Covers K' M₀ (O M) →
        P ⊓ K ≤ K' →
        Nat.card (P ⊓ K ⊓ O K' : Subgroup G) ≤ Nat.card (P ⊓ K ⊓ O K : Subgroup G)) := by
  obtain ⟨K, hK1, hK2, hK3, hK4, hK5, hK6⟩ := exists_K hM₀n hOMn h46 hK hP
  exact exists_K_eq_normalizer hp hp2 hA2 hZA hM hM₀M hOM₀ h413 hzZ hz1 hne hW hP hK1 hK2 hK3 hK4
    hK5 hK6

theorem inf_O_eq_of_le (hp : p.Prime) (hp2 : p ≠ 2) {A Z M M₀ P K K₁ : Subgroup G}
    (hA2 : IsPGroup 2 A) (hZA : Z ≤ A) (hM : M = centralizer (Z : Set G)) (hM₀M : M₀ ≤ M)
    (hOM₀ : O M ≤ M₀)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ → Covers H M₀ (O M) → ∀ z ∈ Z, z ≠ 1 → z ∈ H →
      O H ⊓ C z ≤ O (C z))
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1) (hKtop : K ≠ ⊤) (hPK : IsMaxInvIn p A K (P ⊓ K))
    (hKV : K = normalizer ((P ⊓ K ⊓ O K : Subgroup G) : Set G))
    (hmax₂ : ∀ K' : Subgroup G, CFSG.IsPLocal p K' → A ≤ K' → Covers K' M₀ (O M) →
      P ⊓ K ≤ K' →
      Nat.card (P ⊓ K ⊓ O K' : Subgroup G) ≤ Nat.card (P ⊓ K ⊓ O K : Subgroup G))
    (hK₁ : P ⊓ K ⊔ A ≤ K₁) (hK₁K : K₁ ≤ K) (hcov₁ : Covers K₁ M₀ (O M)) :
    P ⊓ K ⊓ O K₁ = P ⊓ K ⊓ O K := by
  have : Fact p.Prime := ⟨hp⟩
  have hTK₁ : P ⊓ K ≤ K₁ := le_sup_left.trans hK₁
  have hAK₁ : A ≤ K₁ := le_sup_right.trans hK₁
  have hS : ABGLocalTools.IsSylowOf p (P ⊓ K ⊓ O K₁) (O K₁) :=
    isSylowOf_inf_O_of_isMaxInvIn hp hA2 (hAK₁.trans le_normalizer) (hPK.of_le hTK₁ hK₁K)
  have hAS' : A ≤ normalizer ((P ⊓ K ⊓ O K₁ : Subgroup G) : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨hPK.2.2.1 ha, le_normalizer_O K₁ (hAK₁ ha)⟩
  have hle : P ⊓ K ⊓ O K ≤ P ⊓ K ⊓ O K₁ :=
    le_inf inf_le_left ((le_inf inf_le_right (inf_le_left.trans hTK₁)).trans
      (O_inf_le_O_of_le hK₁K))
  have hS1 : P ⊓ K ⊓ O K₁ ≠ ⊥ := by
    intro hbot
    apply hKtop
    rw [hKV, le_bot_iff.mp (hle.trans hbot.le)]
    exact normalizer_eq_top_iff.mpr inferInstance
  have hodd : Odd (Nat.card (P ⊓ K ⊓ O K₁ : Subgroup G)) := by
    obtain ⟨n, hn⟩ := hS.isPGroup.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hcard := hmax₂ (normalizer ((P ⊓ K ⊓ O K₁ : Subgroup G) : Set G))
    ⟨_, hS1, hS.isPGroup, rfl⟩ hAS'
    (covers_normalizer_of_isSylowOf_O hp hA2 hZA hM hM₀M hOM₀ h413 hzZ hz1
      (fun h => hKtop (eq_top_iff.mpr (h ▸ hK₁K))) hAK₁ hcov₁ hS hAS')
    (fun t ht => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer ht, le_normalizer_O K₁ (hTK₁ ht)⟩)
  have hle' : P ⊓ K ⊓ O K₁ ≤
      P ⊓ K ⊓ O (normalizer ((P ⊓ K ⊓ O K₁ : Subgroup G) : Set G)) :=
    le_inf inf_le_left (le_O_of_le_normalizer le_normalizer le_rfl hodd)
  exact (eq_of_le_of_card_ge hle ((card_le_of_le hle').trans hcard)).symm

end Orientation

section Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}

omit [Finite G] in
theorem le_C_of_mem (hA : IsE16 A) {a : G} (ha : a ∈ A) : A ≤ C a := fun _ hb =>
  mem_centralizer_singleton_iff.mpr (G4b.comm_of_isE16 hA hb ha)

theorem M_le_C {x : G} (hx : x ∈ 𝔖.X A) : 𝔖.M A ≤ C x :=
  centralizer_le (Set.singleton_subset_iff.mpr hx)

theorem covers_C {x : G} (hx : x ∈ 𝔖.X A) : Covers (C x) (𝔖.M₀ A) (O (𝔖.M A)) :=
  fun _ hm => mem_sup_left ⟨M_le_C 𝔖 hx (M₀_le 𝔖 A hm), hm⟩

theorem covers_normalizer_of_isSylowOf (hA : IsE16 A) {p : ℕ} (hp : p.Prime) {x : G}
    (hx : x ∈ 𝔖.X A) {T : Subgroup G} (hT : ABGLocalTools.IsSylowOf p T (O (C x)))
    (hAT : A ≤ normalizer (T : Set G)) :
    Covers (normalizer (T : Set G)) (𝔖.M₀ A) (O (𝔖.M A)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hXC : 𝔖.X A ≤ C x := (G4b.X_le_A 𝔖).trans (le_C_of_mem hA hx.1)
  have hXN : 𝔖.X A ≤ normalizer ((C x ⊓ normalizer (T : Set G) : Subgroup G) : Set G) :=
    fun z hz => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer (hXC hz), le_normalizer (hAT hz.1)⟩
  have h := covers_of_eq_O_sup ((isPGroup_of_isE16 hA).to_le (G4b.X_le_A 𝔖)) hXC hXN inf_le_left
    (eq_sup_inf_normalizer_of_isSylowOf (map_subtype_le _) (le_normalizer_O _) hT) rfl
    (M₀_le 𝔖 A) (O_M_le_M₀ 𝔖 A) (O_inf_le_O_of_le (M_le_C 𝔖 hx)) (covers_C 𝔖 hx)
  unfold Covers at h ⊢
  exact h.trans (sup_le_sup_right (inf_le_inf_right _ inf_le_right) _)

theorem exists_pLocal_covers_M₀ (hA : IsE16 A) {p : ℕ} (hp : p.Prime) {D : Subgroup G}
    (hDp : IsPGroup p D) (hAD : A ≤ normalizer (D : Set G))
    (hAD' : ¬ A ≤ centralizer (D : Set G)) (hDgen : XYGenerated (𝔖.X A) (𝔖.Y A) D) :
    ∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K (𝔖.M₀ A) (O (𝔖.M A)) := by
  obtain ⟨x, hxX, y, hyY, hne⟩ : ∃ x ∈ 𝔖.X A, ∃ y ∈ 𝔖.Y A, D ⊓ O (C x) ⊓ O (C y) ≠ ⊥ := by
    by_contra h
    push Not at h
    apply hAD'
    have hD : D = ⊥ :=
      le_bot_iff.mp (hDgen.le.trans (xySup_le_of fun x hx _ y hy _ => (h x hx y hy).le))
    intro a _
    rw [hD, mem_centralizer_iff]
    intro d hd
    rw [SetLike.mem_coe, mem_bot] at hd
    rw [hd, one_mul, mul_one]
  have hAC : A ≤ C x := le_C_of_mem hA hxX.1
  obtain ⟨Px, hPx, hDPx⟩ := exists_isMaxInvIn_ge (A := A) (H := C x)
    (inf_le_left.trans (inf_le_right.trans (map_subtype_le _)))
    (hDp.to_le (inf_le_left.trans inf_le_left)) fun a ha =>
      inf_normalizer_le_normalizer_inf ⟨inf_normalizer_le_normalizer_inf
        ⟨hAD ha, le_normalizer_O _ (hAC ha)⟩, le_normalizer_O _ (le_C_of_mem hA hyY.1 ha)⟩
  have hQ := isSylowOf_inf_O_of_isMaxInvIn hp (isPGroup_of_isE16 hA) (hAC.trans le_normalizer)
    hPx
  have hAQ : A ≤ normalizer ((Px ⊓ O (C x) : Subgroup G) : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨hPx.2.2.1 ha, le_normalizer_O _ (hAC ha)⟩
  refine ⟨normalizer ((Px ⊓ O (C x) : Subgroup G) : Set G),
    ⟨Px ⊓ O (C x), fun hbot => hne ?_, hQ.isPGroup, rfl⟩, hAQ,
    covers_normalizer_of_isSylowOf 𝔖 hA hp hxX hQ hAQ⟩
  rw [eq_bot_iff, ← hbot]
  exact le_inf hDPx (inf_le_left.trans inf_le_right)

variable (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
include hAS hA

theorem C_ne_top {x : G} (hx : x ∈ 𝔖.X A) (hx1 : x ≠ 1) : C x ≠ ⊤ := by
  intro htop
  obtain ⟨x', hx', hx'1, hx'x⟩ := exists_mem_ne_one_ne (G4b.isKleinFour_X 𝔖 hAS hA) x
  obtain ⟨g, hg⟩ := isConj_iff.mp (𝔖.fusion.conj₁ x hx.2 x' hx'.2
    (G4b.orderOf_eq_two_of_isE16 hA hx.1 hx1) (G4b.orderOf_eq_two_of_isE16 hA hx'.1 hx'1))
  have hgx : g ∈ C x := by
    rw [htop]
    exact mem_top g
  rw [mem_centralizer_singleton_iff] at hgx
  apply hx'x
  rw [← hg, hgx, mul_inv_cancel_right]

theorem Y_le_centralizer_of {p : ℕ}
    (h51 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H →
      (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → (∃ x ∈ 𝔖.X A, x ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
        A ≤ normalizer (P : Set G) ∧ P ≤ O (C x) ∧ ¬ 𝔖.Y A ≤ centralizer (P : Set G)) →
        Sec4Setting.PConstrainedWrt p A H (𝔖.Y A)) ∧
      (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → (∃ y ∈ 𝔖.Y A, y ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
        A ≤ normalizer (P : Set G) ∧ P ≤ O (C y) ∧ ¬ 𝔖.X A ≤ centralizer (P : Set G)) →
        Sec4Setting.PConstrainedWrt p A H (𝔖.X A)))
    (hx : ∀ x ∈ 𝔖.X A, x ≠ 1 → ¬ Sec4Setting.PConstrainedWrt p A (C x) (𝔖.Y A))
    {D : Subgroup G} (hDp : IsPGroup p D) (hAD : A ≤ normalizer (D : Set G))
    (hDgen : XYGenerated (𝔖.X A) (𝔖.Y A) D) : 𝔖.Y A ≤ centralizer (D : Set G) := by
  rw [le_centralizer_iff]
  refine hDgen.le.trans (xySup_le_of fun x hxX hx1 y hyY _ => ?_)
  show D ⊓ O (C x) ⊓ O (C y) ≤ centralizer (𝔖.Y A : Set G)
  rw [← le_centralizer_iff]
  by_contra hY
  refine hx x hxX hx1 ((h51 (C x) (C_ne_top 𝔖 hAS hA hxX hx1) (le_C_of_mem hA hxX.1)).1
    (covers_C 𝔖 hxX) ⟨x, hxX, hx1, D ⊓ O (C x) ⊓ O (C y),
      inf_le_left.trans (inf_le_right.trans (map_subtype_le _)),
      hDp.to_le (inf_le_left.trans inf_le_left), fun a ha => ?_,
      inf_le_left.trans inf_le_right, hY⟩)
  exact inf_normalizer_le_normalizer_inf ⟨inf_normalizer_le_normalizer_inf
    ⟨hAD ha, le_normalizer_O _ (le_C_of_mem hA hxX.1 ha)⟩,
    le_normalizer_O _ (le_C_of_mem hA hyY.1 ha)⟩

variable (h48ii : ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A))
  (hN₀ : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) fun L _ => IsKleinFour L)
include h48ii hN₀

theorem N₀_le_of : 𝔖.N₀ A ≤ 𝔖.X A ⊔ O (𝔖.N A) :=
  le_sup_of_quotIs_kleinFour hN₀ (card_O_odd _)
    ((inf_le_right : 𝔖.X A ≤ 𝔖.S₁).trans h48ii.le)
    (@IsKleinFour.card_four _ _ (G4b.isKleinFour_X 𝔖 hAS hA))

theorem covers_N₀_of {H : Subgroup G} (hAH : A ≤ H) : Covers H (𝔖.N₀ A) (O (𝔖.N A)) :=
  (N₀_le_of 𝔖 hAS hA h48ii hN₀).trans (sup_le_sup_right
    (le_inf ((inf_le_left : 𝔖.X A ≤ A).trans hAH) ((inf_le_right : 𝔖.X A ≤ 𝔖.S₁).trans h48ii.le))
    _)

theorem isCovering_iff_of {p : ℕ} {H : Subgroup G} :
    𝔖.IsCovering p A H ↔ 𝔖.IsCoveringFirst p A H :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, covers_N₀_of 𝔖 hAS hA h48ii hN₀ h.1.2.1⟩⟩

theorem isCovering_of {p : ℕ} {K P : Subgroup G} (hK : CFSG.IsPLocal p K) (hAK : A ≤ K)
    (hcov : Covers K (𝔖.M₀ A) (O (𝔖.M A))) (hP : IsMaxInvIn p A ⊤ P) (hPK : P ≤ K) :
    𝔖.IsCovering p A K :=
  ⟨⟨hK, hAK, P, hP, hPK⟩, hcov, covers_N₀_of 𝔖 hAS hA h48ii hN₀ hAK⟩

theorem not_pConstrainedWrt_Y_of {p : ℕ}
    (h52i : (∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H (𝔖.M₀ A) (O (𝔖.M A)) ∧
        Sec4Setting.PConstrainedWrt p A H (𝔖.Y A)) →
      ∀ P, IsMaxInvIn p A ⊤ P →
        𝔖.IsCoveringFirst p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
          Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G))
            (𝔖.Y A))
    (hno : ¬ ∃ H, 𝔖.IsCovering p A H) {P : Subgroup G} (hP : IsMaxInvIn p A ⊤ P)
    {K : Subgroup G} (hK : CFSG.IsPLocal p K) (hAK : A ≤ K)
    (hcov : Covers K (𝔖.M₀ A) (O (𝔖.M A))) :
    ¬ Sec4Setting.PConstrainedWrt p A K (𝔖.Y A) := by
  intro hcon
  obtain ⟨hH, -⟩ := h52i ⟨K, hK, hAK, hcov, hcon⟩ P hP
  exact hno ⟨_, (isCovering_iff_of 𝔖 hAS hA h48ii hN₀).mpr hH⟩

theorem not_le_C_of {p : ℕ} (hp : p.Prime)
    (h51 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H →
      (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → (∃ x ∈ 𝔖.X A, x ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
        A ≤ normalizer (P : Set G) ∧ P ≤ O (C x) ∧ ¬ 𝔖.Y A ≤ centralizer (P : Set G)) →
        Sec4Setting.PConstrainedWrt p A H (𝔖.Y A)) ∧
      (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → (∃ y ∈ 𝔖.Y A, y ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
        A ≤ normalizer (P : Set G) ∧ P ≤ O (C y) ∧ ¬ 𝔖.X A ≤ centralizer (P : Set G)) →
        Sec4Setting.PConstrainedWrt p A H (𝔖.X A)))
    (hx : ∀ x ∈ 𝔖.X A, x ≠ 1 → ¬ Sec4Setting.PConstrainedWrt p A (C x) (𝔖.Y A))
    (hno : ¬ ∃ H, 𝔖.IsCovering p A H) {D : Subgroup G} (hDp : IsPGroup p D)
    (hAD : A ≤ normalizer (D : Set G)) (hAD' : ¬ A ≤ centralizer (D : Set G))
    (hDgen : XYGenerated (𝔖.X A) (𝔖.Y A) D) {P : Subgroup G} (hP : IsMaxInvIn p A ⊤ P)
    (hDP : D ≤ P) {x : G} (hxX : x ∈ 𝔖.X A) (hx1 : x ≠ 1) : ¬ P ≤ C x := by
  intro hPx
  have hAC : A ≤ C x := le_C_of_mem hA hxX.1
  have hQ : ABGLocalTools.IsSylowOf p (P ⊓ O (C x)) (O (C x)) :=
    isSylowOf_inf_O_of_isMaxInvIn hp (isPGroup_of_isE16 hA) (hAC.trans le_normalizer)
      (hP.of_le hPx le_top)
  have hAQ : A ≤ normalizer ((P ⊓ O (C x) : Subgroup G) : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨hP.2.2.1 ha, le_normalizer_O _ (hAC ha)⟩
  by_cases hQ1 : P ⊓ O (C x) = ⊥
  ·
    apply hAD'
    rw [← G4b.X_sup_Y 𝔖 hAS hA]
    refine sup_le ?_ (Y_le_centralizer_of 𝔖 hAS hA h51 hx hDp hAD hDgen)
    rw [le_centralizer_iff]
    refine hDgen.le.trans (xySup_le_of fun x' hx' hx'1 y _ _ => ?_)
    show D ⊓ O (C x') ⊓ O (C y) ≤ centralizer (𝔖.X A : Set G)
    by_cases hxx' : x' = x
    · rw [hxx']
      calc D ⊓ O (C x) ⊓ O (C y) ≤ P ⊓ O (C x) := inf_le_left.trans (inf_le_inf_right _ hDP)
        _ = ⊥ := hQ1
        _ ≤ _ := bot_le
    · refine le_trans ?_ (C_inf_C_le_centralizer (G4b.isKleinFour_X 𝔖 hAS hA) hxX hx1 hx' hx'1
        (Ne.symm hxx'))
      exact le_inf ((inf_le_left.trans (inf_le_left.trans hDP)).trans hPx)
        (inf_le_left.trans (inf_le_right.trans (map_subtype_le _)))
  ·
    refine hno ⟨normalizer ((P ⊓ O (C x) : Subgroup G) : Set G),
      ⟨⟨P ⊓ O (C x), hQ1, hQ.isPGroup, rfl⟩, hAQ, P, hP, fun g hg => ?_⟩,
      covers_normalizer_of_isSylowOf 𝔖 hA hp hxX hQ hAQ, covers_N₀_of 𝔖 hAS hA h48ii hN₀ hAQ⟩
    exact inf_normalizer_le_normalizer_inf ⟨le_normalizer hg, le_normalizer_O _ (hPx hg)⟩

end Setting

end E4b

end CFSG.GH72
