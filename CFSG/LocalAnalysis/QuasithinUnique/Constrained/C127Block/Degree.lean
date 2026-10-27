module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C127Block.PermAux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C127Block.Shape
public import CFSG.Quasithin.Background.FFC10C
public import CFSG.Quasithin.Background.G64Realize

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L246C127

namespace C127Block

theorem young_conj_invariant_or_pow2 {Γ : Type*} [Group Γ] {n : ℕ} (hodd : Odd n) (h5 : 5 ≤ n)
    (a : Fin n) (π : Equiv.Perm (Fin n) →* Γ) (hπ : Function.Injective π)
    (T₁ : Subgroup Γ) (hT₁ : IsPGroup 2 T₁)
    (h1 : ∀ t ∈ T₁, ∀ σ : Equiv.Perm (Fin n), ∃ τ : Equiv.Perm (Fin n), t * π σ * t⁻¹ = π τ)
    (h2 : ∀ t ∈ T₁, ∀ σ τ : Equiv.Perm (Fin n), t * π σ * t⁻¹ = π τ → (σ a = a ↔ τ a = a)) :
    (∃ O : Finset (Fin n), 2 ≤ O.card ∧ O.card + 2 ≤ n ∧
        ∀ t ∈ T₁, ∀ σ ∈ young O, ∃ τ ∈ young O, t * π σ * t⁻¹ = π τ) ∨
      ∃ j : ℕ, n = 2 ^ j + 1 := by
  classical
  have hφ : ∀ t ∈ T₁, ∃ f : Equiv.Perm (Fin n), ∀ σ, π (f * σ * f⁻¹) = t * π σ * t⁻¹ := by
    intro t ht
    choose φ hφ using h1 t ht
    have hmul : ∀ σ τ, φ (σ * τ) = φ σ * φ τ := by
      intro σ τ
      apply hπ
      rw [← hφ (σ * τ), map_mul π (φ σ) (φ τ), ← hφ σ, ← hφ τ, map_mul]
      group
    have h0 : ∀ σ, φ σ a = a ↔ σ a = a := fun σ => (h2 t ht σ (φ σ) (hφ σ)).symm
    obtain ⟨f, hf⟩ := perm_map_stab_inner (by omega) a φ hmul h0
    exact ⟨f, fun σ => by rw [← hf σ, hφ]⟩
  let S₁ : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {f | ∃ t ∈ T₁, ∀ σ, π (f * σ * f⁻¹) = t * π σ * t⁻¹}
      one_mem' := ⟨1, T₁.one_mem, fun σ => by simp⟩
      mul_mem' := by
        rintro f g ⟨t, ht, hf⟩ ⟨t', ht', hg⟩
        refine ⟨t * t', T₁.mul_mem ht ht', fun σ => ?_⟩
        have e : f * g * σ * (f * g)⁻¹ = f * (g * σ * g⁻¹) * f⁻¹ := by group
        rw [e, hf, hg]
        group
      inv_mem' := by
        rintro f ⟨t, ht, hf⟩
        refine ⟨t⁻¹, T₁.inv_mem ht, fun σ => ?_⟩
        have e := hf (f⁻¹ * σ * f)
        have e2 : f * (f⁻¹ * σ * f) * f⁻¹ = σ := by group
        rw [e2] at e
        have e3 : t⁻¹ * π σ * t = π (f⁻¹ * σ * f) := by
          calc t⁻¹ * π σ * t = t⁻¹ * (t * π (f⁻¹ * σ * f) * t⁻¹) * t := by rw [← e]
            _ = π (f⁻¹ * σ * f) := by group
        rw [inv_inv, inv_inv]
        exact e3.symm }
  have hS₁2 : IsPGroup 2 S₁ := by
    intro f
    obtain ⟨t, ht, hf⟩ := f.2
    obtain ⟨k, hk⟩ := hT₁ ⟨t, ht⟩
    refine ⟨k, ?_⟩
    have hpow : ∀ m : ℕ, ∀ σ, π ((f : Equiv.Perm (Fin n)) ^ m * σ * ((f : Equiv.Perm (Fin n)) ^ m)⁻¹) =
        t ^ m * π σ * (t ^ m)⁻¹ := by
      intro m
      induction m with
      | zero => intro σ; simp
      | succ m ih =>
        intro σ
        have e : (f : Equiv.Perm (Fin n)) ^ (m + 1) * σ * ((f : Equiv.Perm (Fin n)) ^ (m + 1))⁻¹ =
            (f : Equiv.Perm (Fin n)) * ((f : Equiv.Perm (Fin n)) ^ m * σ *
              ((f : Equiv.Perm (Fin n)) ^ m)⁻¹) * (f : Equiv.Perm (Fin n))⁻¹ := by
          rw [pow_succ']
          group
        rw [e, hf, ih]
        rw [pow_succ']
        group
    have ht1 : t ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hcomm : ∀ σ, (f : Equiv.Perm (Fin n)) ^ (2 ^ k) * σ = σ * (f : Equiv.Perm (Fin n)) ^ (2 ^ k) := by
      intro σ
      have h1 : π ((f : Equiv.Perm (Fin n)) ^ (2 ^ k) * σ * ((f : Equiv.Perm (Fin n)) ^ (2 ^ k))⁻¹) =
          π σ := by
        rw [hpow, ht1]
        simp
      have h2 := hπ h1
      calc (f : Equiv.Perm (Fin n)) ^ (2 ^ k) * σ
          = ((f : Equiv.Perm (Fin n)) ^ (2 ^ k) * σ * ((f : Equiv.Perm (Fin n)) ^ (2 ^ k))⁻¹) *
              (f : Equiv.Perm (Fin n)) ^ (2 ^ k) := by group
        _ = σ * (f : Equiv.Perm (Fin n)) ^ (2 ^ k) := by rw [h2]
    have h3 := perm_commutes_all_eq_one (by omega) _ hcomm
    exact Subtype.ext (by simpa using h3)
  rcases perm_two_subgroup_dichotomy hodd h5 S₁ hS₁2 with ⟨O, hOinv, hO2, hOn⟩ | hj
  · left
    refine ⟨O, hO2, hOn, fun t ht σ hσ => ?_⟩
    obtain ⟨f, hf⟩ := hφ t ht
    have hfS : f ∈ S₁ := ⟨t, ht, hf⟩
    have hfy : f ∈ young O := mem_young_of_forall_mem O (hOinv f hfS)
    exact ⟨f * σ * f⁻¹, (young O).mul_mem ((young O).mul_mem hfy hσ) ((young O).inv_mem hfy), (hf σ).symm⟩
  · right
    exact hj

theorem mem_sup_of_forall_commute {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have e : b * a' = a' * b := (h a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [e]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have e : b * a = a * b := (h a ha b hb).symm
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := by
            have : a * b⁻¹ = b⁻¹ * a := by
              calc a * b⁻¹ = b⁻¹ * (b * a) * b⁻¹ := by group
                _ = b⁻¹ * (a * b) * b⁻¹ := by rw [e]
                _ = b⁻¹ * a := by group
            calc b⁻¹ * a⁻¹ = (a * b)⁻¹ := by group
              _ = (b * a)⁻¹ := by rw [e]
              _ = a⁻¹ * b⁻¹ := by group }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem blk_inf_eq_bot_of_ctx {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hP4 : AsB15Part4) {X T M : Subgroup (MulAut V)} (hctx : B69.ShapeCtx X T M)
    (hO2 : pCoreOf 2 X = ⊥)
    (hact : ∀ L' : Subgroup (MulAut V), CFSG.Open.IsComponentOf L' X →
      ∃ A, IsFFStarMin X A ∧ ⁅L', A⁆ = L')
    {L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X) :
    B69.blk X L ⊓ (⨆ (L' : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L' X ∧ L' ≠ L),
      B69.blk X L') = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot]
  have hxX : x ∈ X := B69.blk_le_X hL hx1
  have hxW : ∀ w ∈ commV L, x w = w := by
    have hle : (⨆ (L' : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L' X ∧ L' ≠ L),
        B69.blk X L') ≤ centSub (commV L) :=
      iSup₂_le fun L' hL' => B69.blk_le_centSub hV hP4 hctx hL'.1 hL (hact L hL) hL'.2
    exact fun w hw => hle hx2 w hw
  have hxU : ∀ u ∈ B69.vSigma X, x u = u := by
    have hle : B69.vSigma X ≤ MonoidHom.eqLocus x.toMonoidHom (MonoidHom.id V) := by
      refine iSup₂_le fun L'' hL'' w hw => ?_
      by_cases hLL : L'' = L
      · subst hLL
        exact hxW w hw
      · exact B69.blk_le_centSub hV hP4 hctx hL hL'' (hact L'' hL'') (Ne.symm hLL) hx1 w hw
    exact fun u hu => hle hu
  have hxQ : ∀ v : V, x v * v⁻¹ ∈ B69.vSigma X := fun v =>
    B69.centQuot_mono (B69.commV_le_vSigma hL)
      (B69.blk_le_centQuot hV hctx hL (hact L hL) hx1) v
  exact B69.eq_one_of_stab hV hO2 (B69.vSigma_invariant X) hxX hxU hxQ

theorem altDegree_core {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hP4 : AsB15Part4) {X T M A L : Subgroup (MulAut V)} (hctx : B69.ShapeCtx X T M)
    (hmp : MinParabolic X T M) (hO2 : pCoreOf 2 X = ⊥)
    (hact : ∀ L' : Subgroup (MulAut V), CFSG.Open.IsComponentOf L' X →
      ∃ A', IsFFStarMin X A' ∧ ⁅L', A'⁆ = L')
    (hL : CFSG.Open.IsComponentOf L X) (hblk : B69.blk X L = L ⊔ A) {k : ℕ} (hk : 2 ≤ k)
    (π : Equiv.Perm (Fin (2 * k + 1)) →* ↥(L ⊔ A)) (hinj : Function.Injective π)
    (hsurj : Function.Surjective π)
    (hLeq : L = (alternatingGroup (Fin (2 * k + 1))).map ((L ⊔ A).subtype.comp π))
    (hM : (M ⊓ (L ⊔ A)).subgroupOf (L ⊔ A) =
      (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1)))
        (⟨0, by omega⟩ : Fin (2 * k + 1))).map π) :
    ∃ j : ℕ, 2 * k = 2 ^ j := by
  classical
  have hn5 : 5 ≤ 2 * k + 1 := by omega
  have hnodd : Odd (2 * k + 1) := odd_two_mul_add_one k
  set a : Fin (2 * k + 1) := ⟨0, by omega⟩ with ha
  let π' : Equiv.Perm (Fin (2 * k + 1)) →* MulAut V := (L ⊔ A).subtype.comp π
  have hπ'inj : Function.Injective π' := fun x y h => hinj (Subtype.ext h)
  have hπ'mem : ∀ σ, π' σ ∈ L ⊔ A := fun σ => (π σ).2
  have hrange : ∀ x ∈ L ⊔ A, ∃ σ, π' σ = x := by
    intro x hx
    obtain ⟨σ, hσ⟩ := hsurj ⟨x, hx⟩
    exact ⟨σ, congrArg Subtype.val hσ⟩
  have hMiff : ∀ σ, π' σ ∈ M ↔ σ a = a := by
    intro σ
    have h1 : π σ ∈ (M ⊓ (L ⊔ A)).subgroupOf (L ⊔ A) ↔
        π σ ∈ (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1))) a).map π := by rw [hM]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h1
    constructor
    · intro hσ
      obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.1 (h1.1 ⟨hσ, (π σ).2⟩)
      have : τ = σ := hinj hτσ
      subst this
      simpa [MulAction.mem_stabilizer_iff] using hτ
    · intro hσ
      exact (h1.2 (Subgroup.mem_map.2 ⟨σ, by simpa [MulAction.mem_stabilizer_iff] using hσ, rfl⟩)).1
  have hTX : T ≤ X := hmp.isSylow.1
  have hTM : T ≤ M := hmp.le
  have hT2 : IsPGroup 2 T := hmp.isSylow.2.1
  let T₁ : Subgroup (MulAut V) := T ⊓ Subgroup.normalizer (L : Set (MulAut V))
  have hT₁2 : IsPGroup 2 T₁ := hT2.to_le inf_le_left
  have hconjH : ∀ t ∈ T₁, B6.conjSub t (L ⊔ A) = L ⊔ A := by
    intro t ht
    rw [← hblk, B69.conjSub_blk (hTX ht.1), B6.conjSub_eq_self ht.2]
  have hcl : ∀ t ∈ T₁, ∀ x ∈ L ⊔ A, t * x * t⁻¹ ∈ L ⊔ A := by
    intro t ht x hx
    have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
    have : t * x * t⁻¹ ∈ B6.conjSub t (L ⊔ A) := B6.mem_conjSub.2 (by rw [e]; exact hx)
    rwa [hconjH t ht] at this
  have h1 : ∀ t ∈ T₁, ∀ σ : Equiv.Perm (Fin (2 * k + 1)), ∃ τ : Equiv.Perm (Fin (2 * k + 1)),
      t * π' σ * t⁻¹ = π' τ := fun t ht σ =>
    (hrange _ (hcl t ht _ (hπ'mem σ))).imp fun τ h => h.symm
  have h2 : ∀ t ∈ T₁, ∀ σ τ : Equiv.Perm (Fin (2 * k + 1)), t * π' σ * t⁻¹ = π' τ →
      (σ a = a ↔ τ a = a) := by
    intro t ht σ τ hτ
    rw [← hMiff σ, ← hMiff τ, ← hτ]
    have htM : t ∈ M := hTM ht.1
    constructor
    · intro hσ
      exact M.mul_mem (M.mul_mem htM hσ) (M.inv_mem htM)
    · intro hσ
      have := M.mul_mem (M.mul_mem (M.inv_mem htM) hσ) htM
      simpa [mul_assoc] using this
  rcases young_conj_invariant_or_pow2 hnodd hn5 a π' hπ'inj T₁ hT₁2 h1 h2 with
    ⟨O, hO2', hOn, hinv⟩ | ⟨j, hj⟩
  swap
  · exact ⟨j, by omega⟩
  exfalso
  have hHX : L ⊔ A ≤ X := hblk ▸ B69.blk_le_X hL
  have hmemconj : ∀ (t x : MulAut V) (S : Subgroup (MulAut V)), x ∈ S → t * x * t⁻¹ ∈ B6.conjSub t S := by
    intro t x S hx
    have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
    exact B6.mem_conjSub.2 (by rw [e]; exact hx)
  let Y : Subgroup (MulAut V) := (young O).map π'
  have hYmem : ∀ σ ∈ young O, π' σ ∈ Y := fun σ hσ => ⟨σ, hσ, rfl⟩
  have hYH : Y ≤ L ⊔ A := by
    rintro _ ⟨σ, -, rfl⟩
    exact hπ'mem σ
  have hYconj : ∀ t ∈ T₁, ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := by
    rintro t ht _ ⟨σ, hσ, rfl⟩
    obtain ⟨τ, hτ, hτe⟩ := hinv t ht σ hσ
    exact ⟨τ, hτ, hτe.symm⟩
  let J' : Subgroup (MulAut V) := ⨆ (L' : Subgroup (MulAut V))
    (_ : CFSG.Open.IsComponentOf L' X ∧ L' ≠ L), B69.blk X L'
  have hJ'cent : J' ≤ Subgroup.centralizer ((L ⊔ A : Subgroup (MulAut V)) : Set (MulAut V)) := by
    refine iSup₂_le fun L' hL' x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hblk] at hy
    exact B69.blk_commute hV hP4 hctx hL hL'.1 hL'.2.symm y hy x hx
  have hcomm : ∀ y ∈ L ⊔ A, ∀ j ∈ J', y * j = j * y := fun y hy j hj =>
    Subgroup.mem_centralizer_iff.1 (hJ'cent hj) y hy
  have hind : (L ⊔ A) ⊓ J' = ⊥ := by
    have := blk_inf_eq_bot_of_ctx hV hP4 hctx hO2 hact hL
    rwa [hblk] at this
  let D : Subgroup (MulAut V) := ⨆ t ∈ T, B6.conjSub t Y
  have hYD : Y ≤ D := by
    have : B6.conjSub 1 Y ≤ D :=
      le_iSup₂_of_le (f := fun t (_ : t ∈ T) => B6.conjSub t Y) 1 T.one_mem le_rfl
    simpa [B6.conjSub_one] using this
  have hDle : D ≤ Y ⊔ J' := by
    refine iSup₂_le fun t ht z hz => ?_
    by_cases htL : B6.conjSub t L = L
    · have htN : t ∈ Subgroup.normalizer (L : Set (MulAut V)) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          have := hmemconj t x L hx
          rwa [htL] at this
        · intro hx
          rw [← htL] at hx
          have := B6.mem_conjSub.1 hx
          have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
          rwa [e] at this
      have hz' : t⁻¹ * z * t ∈ Y := B6.mem_conjSub.1 hz
      have := hYconj t ⟨ht, htN⟩ _ hz'
      have e : t * (t⁻¹ * z * t) * t⁻¹ = z := by group
      rw [e] at this
      exact Subgroup.mem_sup_left this
    · have hcomp' : CFSG.Open.IsComponentOf (B6.conjSub t L) X :=
        B113.isComponentOf_conj hL (hTX ht)
      have h3 : B6.conjSub t Y ≤ B69.blk X (B6.conjSub t L) := by
        rw [← B69.conjSub_blk (hTX ht), hblk]
        exact (B6.conjSub t).monotone hYH
      have h4 : B69.blk X (B6.conjSub t L) ≤ J' :=
        le_iSup₂_of_le (f := fun (L' : Subgroup (MulAut V))
          (_ : CFSG.Open.IsComponentOf L' X ∧ L' ≠ L) => B69.blk X L') (B6.conjSub t L)
          ⟨hcomp', htL⟩ le_rfl
      exact Subgroup.mem_sup_right (h4 (h3 hz))
  have hTD : ∀ s ∈ T, ∀ x ∈ D, s * x * s⁻¹ ∈ D := by
    intro s hs x hx
    have hle : B6.conjSub s D ≤ D := by
      simp only [D, OrderIso.map_iSup]
      refine iSup₂_le fun t ht => ?_
      rw [← B6.conjSub_mul]
      exact le_iSup₂_of_le (f := fun t (_ : t ∈ T) => B6.conjSub t Y) (s * t) (T.mul_mem hs ht)
        le_rfl
    exact hle (hmemconj s x D hx)
  have hTnorm : T ≤ Subgroup.normalizer (D : Set (MulAut V)) := fun s hs =>
    B6.mem_normalizer_of_forall_mem (hTD s hs) (fun x hx => by
      simpa using hTD s⁻¹ (T.inv_mem hs) x hx)
  have hDX : D ≤ X := by
    refine iSup₂_le fun t ht z hz => ?_
    have hz' : t⁻¹ * z * t ∈ Y := B6.mem_conjSub.1 hz
    have hz'' : t⁻¹ * z * t ∈ X := hHX (hYH hz')
    have e : t * (t⁻¹ * z * t) * t⁻¹ = z := by group
    rw [← e]
    exact X.mul_mem (X.mul_mem (hTX ht) hz'') (X.inv_mem (hTX ht))
  by_cases hXD : X ≤ Subgroup.normalizer (D : Set (MulAut V))
  ·
    rcases hmp.le_kerIn_or_twoResidual_le hDX hXD with hker | hres
    · obtain ⟨σ₀, hσ₀, hσ₀1, hσ₀2⟩ := exists_involution_mem_young O (by omega)
      have hmem : π' σ₀ ∈ kerIn M X := hker (hYD (hYmem σ₀ hσ₀))
      have hsq : (π' σ₀) ^ 2 = 1 := by rw [pow_two, ← map_mul, hσ₀2, map_one]
      have hp2 : IsPGroup 2 (Subgroup.zpowers (π' σ₀)) := by
        obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
          (by simpa using orderOf_dvd_of_pow_eq_one hsq : orderOf (π' σ₀) ∣ 2 ^ 1)
        exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
      have hz := hmp.le_pCoreOf_of_isPGroup_of_le_kerIn hp2 (Subgroup.zpowers_le.2 hmem)
      rw [hO2] at hz
      have h1 : π' σ₀ = 1 := Subgroup.mem_bot.1 (hz (Subgroup.mem_zpowers _))
      exact hσ₀1 (hπ'inj (by rw [h1, map_one]))
    · have hLD : L ≤ D := (B69.component_le_twoResidual hL).trans hres
      have hLY : ∀ x ∈ L, x ∈ Y := by
        intro x hx
        have hxH : x ∈ L ⊔ A := Subgroup.mem_sup_left hx
        obtain ⟨y, hy, j, hj, hxe⟩ := mem_sup_of_forall_commute
          (fun y hy j hj => hcomm y (hYH hy) j hj) (hDle (hLD hx))
        have hjH : j ∈ L ⊔ A := by
          have : j = y⁻¹ * x := by rw [hxe]; group
          rw [this]
          exact (L ⊔ A).mul_mem ((L ⊔ A).inv_mem (hYH hy)) hxH
        have hj1 : j = 1 := by
          have : j ∈ (L ⊔ A) ⊓ J' := ⟨hjH, hj⟩
          rw [hind] at this
          exact Subgroup.mem_bot.1 this
        rw [hxe, hj1, mul_one]
        exact hy
      obtain ⟨σ, hσA, hσ⟩ := exists_even_not_mem_young O hO2' hOn
      apply hσ
      have hmemL : π' σ ∈ L := hLeq.ge (Subgroup.mem_map.2 ⟨σ, hσA, rfl⟩)
      obtain ⟨τ, hτ, hτe⟩ := hLY _ hmemL
      have : τ = σ := hπ'inj hτe
      rw [this] at hτ
      exact hτ
  ·
    have hR : X ⊓ Subgroup.normalizer (D : Set (MulAut V)) < X :=
      lt_of_le_of_ne inf_le_left (fun h => hXD (le_trans (le_of_eq h.symm) inf_le_right))
    have hRM := hmp.le_of_lt (le_inf hTX hTnorm) hR
    obtain ⟨σ, hσ, hσa⟩ := exists_mem_young_moves O hO2' hOn a
    have hσD : π' σ ∈ D := hYD (hYmem σ hσ)
    have : π' σ ∈ M := hRM ⟨hDX hσD, Subgroup.le_normalizer hσD⟩
    exact hσa ((hMiff σ).1 this)

end C127Block

end L246C127

end CFSG.QuasithinUnique

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.L246C127
open scoped commutatorElement

theorem asB69AltDegree_of (hP4 : AsB15Part4) (hComp : B69.AsB69ComponentK) :
    B69.AsB69AltDegree := by
  intro V _ _ hV X T M A L hCH W hW k hk hAlt
  obtain ⟨hK, hmp, hO2, hFF, hns, hA, hL, hLA⟩ := hCH
  have hctx : B69.ShapeCtx X T M := C127Block.shapeCtxK_of_component hComp hV hK hmp hO2 hFF hns
  have hact := B69.exists_active hV hP4 hmp hO2 hFF hns
  have hshape := hctx A L hA hL hLA W hW
  have hcomm : commV L = W := (B69.commV_eq_of_shape hV hA hL.2.2 hLA hW hshape).1
  subst hcomm
  have hAltS : B69.AltShape M A L (commV L) := B69.altShape_iff.2 ⟨k, hk, hAlt⟩
  have hblk : B69.blk X L = L ⊔ A := by
    apply le_antisymm
    · refine B69.blk_le_iff.2 ⟨le_sup_left, fun A' hA' hLA' => ?_⟩
      exact B69.altBlock_of_ctx hV hP4 hctx hO2 hact hA hL hLA hAltS hA' hLA'
    · exact sup_le B69.le_blk_self (B69.le_blk_of hA hLA)
  have hk2 : 2 ≤ k := C127Block.two_le_of_altShapeK hk hL.2.2 hAlt
  obtain ⟨π, hsurj, hreal, hLeq, -, hM⟩ := hAlt
  have h5 : 5 ≤ 2 * k + 1 := by omega
  have hinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (G64.symDn_faithful h5) hreal
  exact C127Block.altDegree_core hV hP4 hctx hmp hO2 hact hL hblk hk2 π hinj hsurj hLeq hM

end CFSG.Quasithin
