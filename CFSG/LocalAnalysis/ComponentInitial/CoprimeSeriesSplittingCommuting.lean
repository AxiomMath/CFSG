module

public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCentralSeriesSplitting

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem coprime_central_series_central_two_extension_splitting_of_commute
    {T : Type*} [Group T] [Finite T] (hT : Odd (Nat.card T))
    {U : Type*} [Group U] [Finite U] [MulDistribMulAction T U] (hU : IsPGroup 2 U)
    (m : ℕ) (S : ℕ → Subgroup U) (hS0 : S 0 = ⊥) (hSm : S m = ⊤)
    (hmono : ∀ i < m, S i ≤ S (i + 1))
    (hinv : ∀ i ≤ m, ∀ (t : T), ∀ x ∈ S i, t • x ∈ S i)
    (hcent : ∀ i < m, ∀ x ∈ S (i + 1), ∀ g : U, x⁻¹ * g⁻¹ * x * g ∈ S i)
    (hsq : ∀ i < m, ∀ x ∈ S (i + 1), x ^ 2 ∈ S i)
    (hfix : ∀ i < m, ∀ x ∈ S (i + 1), (∀ t : T, (t • x)⁻¹ * x ∈ S i) → x ∈ S i)
    {ι : Type*} (Zs Ys : ι → Set U)
    (hbil : ∀ i < m, ∀ j < m, ∀ b : U → U → ZMod 2,
      (∀ x ∈ S (i + 1), ∀ x' ∈ S (i + 1), ∀ y ∈ S (j + 1), b (x * x') y = b x y + b x' y) →
      (∀ x ∈ S (i + 1), ∀ y ∈ S (j + 1), ∀ y' ∈ S (j + 1), b x (y * y') = b x y + b x y') →
      (∀ x ∈ S i, ∀ y ∈ S (j + 1), b x y = 0) → (∀ x ∈ S (i + 1), ∀ y ∈ S j, b x y = 0) →
      (∀ (t : T), ∀ x ∈ S (i + 1), ∀ y ∈ S (j + 1), b (t • x) (t • y) = b x y) →
      (∀ k, ∀ z ∈ Zs k, ∀ y ∈ Ys k, b z y = 0) →
      ∀ x ∈ S (i + 1), ∀ y ∈ S (j + 1), b x y = 0)
    {P : Type*} [Group P] [Finite P] [MulDistribMulAction T P] (η : P →* U)
    (hη : Function.Surjective η) (hC : η.ker ≤ center P) (h2 : IsPGroup 2 η.ker)
    (hTC : ∀ (t : T), ∀ c ∈ η.ker, t • c = c)
    (hequiv : ∀ (t : T) (x : P), η (t • x) = t • η x)
    (hZY : ∀ k, ∀ a y : P, η a ∈ Zs k → η y ∈ Ys k → a * y = y * a) :
    ∃ K : Subgroup P, (∀ (t : T), ∀ x ∈ K, t • x ∈ K) ∧ K.Normal ∧ IsCompl η.ker K ∧
      Function.Bijective (η.comp K.subtype) := by
  classical
  induction m generalizing U P with
  | zero =>
    have htriv : ∀ u : U, u = 1 := fun u => by
      have hu : u ∈ S 0 := hSm ▸ mem_top u
      rw [hS0] at hu
      exact (mem_bot).1 hu
    have hker : η.ker = ⊤ := eq_top_iff.2 fun x _ => htriv (η x)
    refine ⟨⊥, fun t x hx => ?_, inferInstance, by rw [hker]; exact isCompl_top_bot, ?_, ?_⟩
    · rw [(mem_bot).1 hx, smul_one]
      exact one_mem _
    · intro a b _
      exact Subtype.ext (by rw [(mem_bot).1 a.2, (mem_bot).1 b.2])
    · intro u
      exact ⟨1, by rw [htriv u]; exact map_one _⟩
  | succ m ih =>
    have hle : ∀ i j, i ≤ j → j ≤ m + 1 → S i ≤ S j := by
      intro i j hij hj
      induction j, hij using Nat.le_induction with
      | base => exact le_rfl
      | succ j hij ihj => exact (ihj (by omega)).trans (hmono j (by omega))
    have hZc : ∀ z ∈ S 1, ∀ g : U, z * g = g * z := by
      intro z hz g
      have h := hcent 0 (by omega) z hz g
      rw [hS0, mem_bot] at h
      calc z * g = g * z * (z⁻¹ * g⁻¹ * z * g) := by group
        _ = g * z := by rw [h, mul_one]
    have hZn : (S 1).Normal := ⟨fun z hz g => by rwa [← hZc z hz g, mul_inv_cancel_right]⟩
    set A : Subgroup P := (S 1).comap η with hAdef
    have hcen : ∀ c ∈ η.ker, ∀ g : P, c * g = g * c := fun c hc g =>
      ((mem_center_iff.1 (hC hc)) g).symm
    have hkerA : η.ker ≤ A := fun c hc => by
      rw [mem_comap, (MonoidHom.mem_ker).1 hc]
      exact one_mem _
    have hcmC : ∀ a ∈ A, ∀ x : P, a⁻¹ * x⁻¹ * a * x ∈ η.ker := by
      intro a ha x
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact commutator_eq_one_of_mul_comm (hZc _ ha _)
    have hsqA : ∀ a ∈ A, a ^ 2 ∈ η.ker := by
      intro a ha
      have h := hsq 0 (by omega) (η a) ha
      rw [hS0, mem_bot, ← map_pow] at h
      exact (MonoidHom.mem_ker).2 h
    have hcm2 : ∀ a ∈ A, ∀ x : P, (a⁻¹ * x⁻¹ * a * x) ^ 2 = 1 := by
      intro a ha x
      rw [sq, ← commutator_mul_left hcen (hcmC a ha x), ← sq]
      exact commutator_central_left hcen (hsqA a ha)
    have hcongr : ∀ a a' x x' : P, η a = η a' → η x = η x' →
        a⁻¹ * x⁻¹ * a * x = a'⁻¹ * x'⁻¹ * a' * x' := by
      intro a a' x x' ha hx
      have hca : a⁻¹ * a' ∈ η.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ha, inv_mul_cancel]
      have hcx : x⁻¹ * x' ∈ η.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel]
      have h1 : a' = a * (a⁻¹ * a') := by group
      have h2 : x' = x * (x⁻¹ * x') := by group
      rw [h1, h2, commutator_mul_central_left hcen hca, commutator_mul_central_right hcen hcx]
    set lift := Function.surjInv hη with hliftdef
    have hlift : ∀ u, η (lift u) = u := Function.surjInv_eq hη
    have hliftA : ∀ u ∈ S 1, lift u ∈ A := fun u hu => by
      rw [mem_comap, hlift]
      exact hu
    have hcomm : ∀ j ≤ m + 1, ∀ a ∈ A, ∀ y : P, η y ∈ S j → a * y = y * a := by
      intro j
      induction j with
      | zero =>
        intro _ a _ y hy
        rw [hS0, mem_bot] at hy
        exact (hcen y hy a).symm
      | succ j ihj =>
        intro hj a ha y hy
        by_contra hne
        have hw := hcmC a ha y
        have hw1 : a⁻¹ * y⁻¹ * a * y ≠ 1 := fun h => hne (mul_comm_of_commutator_eq_one h)
        obtain ⟨φ, hφ, hφw⟩ := exists_zmod_two_functional hcen hw (hcm2 a ha y) hw1
        have hφ1 : φ 1 = 0 := by
          have h := hφ 1 (one_mem _) 1 (one_mem _) (one_pow 2) (one_pow 2)
          rw [mul_one] at h
          exact left_eq_add.1 h
        let b : U → U → ZMod 2 := fun u v => φ ((lift u)⁻¹ * (lift v)⁻¹ * lift u * lift v)
        have hb : ∀ a' y' : P, b (η a') (η y') = φ (a'⁻¹ * y'⁻¹ * a' * y') := by
          intro a' y'
          change φ _ = φ _
          rw [hcongr (lift (η a')) a' (lift (η y')) y' (hlift _) (hlift _)]
        have key := hbil 0 (by omega) j (by omega) b ?_ ?_ ?_ ?_ ?_ ?_ (η a) ha (η y) hy
        · exact hφw (by rw [← hb a y]; exact key)
        · intro x hx x' hx' v _
          change φ _ = φ _ + φ _
          rw [hcongr (lift (x * x')) (lift x * lift x') (lift v) (lift v)
            (by rw [hlift, map_mul, hlift, hlift]) rfl,
            commutator_mul_left hcen (hcmC _ (hliftA x hx) _)]
          exact hφ _ (hcmC _ (hliftA x hx) _) _ (hcmC _ (hliftA x' hx') _)
            (hcm2 _ (hliftA x hx) _) (hcm2 _ (hliftA x' hx') _)
        · intro x hx v _ v' _
          change φ _ = φ _ + φ _
          rw [hcongr (lift x) (lift x) (lift (v * v')) (lift v * lift v') rfl
            (by rw [hlift, map_mul, hlift, hlift]),
            commutator_mul_right hcen (hcmC _ (hliftA x hx) _),
            hφ _ (hcmC _ (hliftA x hx) _) _ (hcmC _ (hliftA x hx) _) (hcm2 _ (hliftA x hx) _)
              (hcm2 _ (hliftA x hx) _), add_comm]
        · intro x hx v _
          rw [hS0, mem_bot] at hx
          subst hx
          change φ _ = 0
          rw [commutator_central_left hcen (show lift 1 ∈ η.ker by
            rw [MonoidHom.mem_ker, hlift]), hφ1]
        · intro x hx v hv
          change φ _ = 0
          rw [commutator_eq_one_of_mul_comm (ihj (by omega) _ (hliftA x hx) _
            (by rw [hlift]; exact hv)), hφ1]
        · intro t x hx v _
          change φ _ = φ _
          rw [hcongr (lift (t • x)) (t • lift x) (lift (t • v)) (t • lift v)
            (by rw [hlift, hequiv, hlift]) (by rw [hlift, hequiv, hlift])]
          have hsm : (t • lift x)⁻¹ * (t • lift v)⁻¹ * (t • lift x) * (t • lift v) =
              t • ((lift x)⁻¹ * (lift v)⁻¹ * lift x * lift v) := by
            simp only [smul_mul', smul_inv']
          rw [hsm, hTC t _ (hcmC _ (hliftA x hx) _)]
        · intro k z hz w hw
          change φ _ = 0
          rw [commutator_eq_one_of_mul_comm (hZY k _ _ (by rw [hlift]; exact hz)
            (by rw [hlift]; exact hw)), hφ1]
    have hAcomm : ∀ a ∈ A, ∀ y : P, a * y = y * a := fun a ha y =>
      hcomm (m + 1) le_rfl a ha y (by rw [hSm]; exact mem_top _)
    have hfixA : ∀ a ∈ A, (∀ t : T, t • a = a) → a ∈ η.ker := by
      intro a ha hfa
      have h := hfix 0 (by omega) (η a) ha fun t => by
        rw [← hequiv, hfa t, inv_mul_cancel, hS0]
        exact one_mem _
      rw [hS0, mem_bot] at h
      exact (MonoidHom.mem_ker).2 h
    have hAinv : ∀ (t : T), ∀ a ∈ A, t • a ∈ A := fun t a ha => by
      rw [mem_comap, hequiv]
      exact hinv 1 (by omega) t _ ha
    have hAI : CFSG.IsInvariant T P A :=
      ⟨fun t g => ⟨fun hg => hAinv t g hg, fun hg => by
        have h := hAinv t⁻¹ _ hg
        rwa [inv_smul_smul] at h⟩⟩
    have hcommA : ∀ x y : A, x * y = y * x := fun x y => Subtype.ext (hAcomm x x.2 y)
    have : IsMulCommutative A := ⟨⟨hcommA⟩⟩
    have hA2 : IsPGroup 2 A := by
      rintro ⟨a, ha⟩
      obtain ⟨k, hk⟩ := h2 ⟨a ^ 2, hsqA a ha⟩
      refine ⟨k + 1, Subtype.ext ?_⟩
      have hk' : (a ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [pow_succ', pow_mul]
      exact hk'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hA2
    have hcop : Nat.Coprime (Nat.card T) (Nat.card A) := by
      rw [hn]
      exact Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hT)
    have hsup := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (G := A) (A := T) (Group.isSolvable_of_comm hcommA) hcop
    have hcompl :=
      isCompl_fixedPointSubgroup_commutatorAction_of_sup_eq_top_of_coprime_of_isMulCommutative
        (G := A) (A := T) hsup hcop inferInstance
    set D := commutatorAction T A with hDdef
    set N : Subgroup P := D.map A.subtype with hNdef
    have hgen : ∀ (t : T) (a : P) (ha : a ∈ A), a⁻¹ * (t • a) ∈ N := by
      intro t a ha
      refine ⟨(⟨a, ha⟩ : A)⁻¹ * (t • (⟨a, ha⟩ : A)), ?_, rfl⟩
      rw [hDdef, commutatorAction_eq_closure]
      exact subset_closure ⟨t, ⟨a, ha⟩, rfl⟩
    have hDinv : ∀ (t : T), ∀ d ∈ D, t • d ∈ D := by
      intro t d hd
      rw [hDdef, commutatorAction_eq_closure] at hd ⊢
      induction hd using closure_induction with
      | mem x hx =>
        obtain ⟨s, g, rfl⟩ := hx
        refine subset_closure ⟨t * s * t⁻¹, t • g, ?_⟩
        rw [smul_mul', smul_inv', mul_smul, mul_smul, inv_smul_smul]
      | one => rw [smul_one]; exact one_mem _
      | mul x y _ _ hx hy => rw [smul_mul']; exact mul_mem hx hy
      | inv x _ hx => rw [smul_inv']; exact inv_mem hx
    have hNinv : ∀ (t : T), ∀ x ∈ N, t • x ∈ N := by
      rintro t _ ⟨d, hd, rfl⟩
      exact ⟨t • d, hDinv t d hd, rfl⟩
    have hNC : ∀ x ∈ N, x ∈ η.ker → x = 1 := by
      rintro _ ⟨d, hd, rfl⟩ hdk
      have hdF : d ∈ fixedPointSubgroup T A := fun t => Subtype.ext (hTC t _ hdk)
      rw [disjoint_def.1 hcompl.disjoint hdF hd]
      rfl
    have hAdec : ∀ a ∈ A, ∃ c ∈ η.ker, ∃ n ∈ N, a = c * n := by
      intro a ha
      have hmem : (⟨a, ha⟩ : A) ∈ fixedPointSubgroup T A ⊔ D := by
        rw [hsup]
        exact mem_top _
      have : D.Normal := ⟨fun n hn g => by rwa [hcommA g n, mul_inv_cancel_right]⟩
      rw [← SetLike.mem_coe, mul_normal, Set.mem_mul] at hmem
      obtain ⟨f, hf, d, hd, hfd⟩ := hmem
      exact ⟨f, hfixA f f.2 fun t => congrArg Subtype.val (hf t), d, ⟨d, hd, rfl⟩,
        (congrArg Subtype.val hfd).symm⟩
    have hNn : N.Normal := ⟨fun x hx g => by
      rw [← hAcomm x (map_subtype_le D hx) g, mul_inv_cancel_right]
      exact hx⟩
    have hZI : CFSG.IsInvariant T U (S 1) :=
      ⟨fun t u => ⟨fun h => hinv 1 (by omega) t u h, fun h => by
        have h' := hinv 1 (by omega) t⁻¹ _ h
        rwa [inv_smul_smul] at h'⟩⟩
    have hNI : CFSG.IsInvariant T P N :=
      ⟨fun t x => ⟨fun h => hNinv t x h, fun h => by
        have h' := hNinv t⁻¹ _ h
        rwa [inv_smul_smul] at h'⟩⟩
    let iU : MulDistribMulAction T (U ⧸ S 1) := quotientMulDistribMulAction (S 1) hZI
    let iP : MulDistribMulAction T (P ⧸ N) := quotientMulDistribMulAction N hNI
    have hsmulU : ∀ (t : T) (u : U), t • (u : U ⧸ S 1) = ((t • u : U) : U ⧸ S 1) :=
      fun t u => rfl
    have hsmulP : ∀ (t : T) (x : P), t • (x : P ⧸ N) = ((t • x : P) : P ⧸ N) :=
      fun t x => rfl
    set S' : ℕ → Subgroup (U ⧸ S 1) := fun i => (S (i + 1)).map (QuotientGroup.mk' (S 1))
      with hS'def
    have hmemS' : ∀ i ≤ m, ∀ u : U, (u : U ⧸ S 1) ∈ S' i ↔ u ∈ S (i + 1) := by
      intro i hi u
      constructor
      · rintro ⟨w, hw, hwu⟩
        have h : w⁻¹ * u ∈ S 1 := QuotientGroup.eq.1 hwu
        have hu : u = w * (w⁻¹ * u) := by group
        rw [hu]
        exact mul_mem hw (hle 1 (i + 1) (by omega) (by omega) h)
      · intro hu
        exact ⟨u, hu, rfl⟩
    have hS0' : S' 0 = ⊥ := QuotientGroup.map_mk'_self (S 1)
    have hSm' : S' m = ⊤ := by
      change (S (m + 1)).map _ = ⊤
      rw [hSm]
      exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    have hmono' : ∀ i < m, S' i ≤ S' (i + 1) := fun i _ => map_mono (hmono (i + 1) (by omega))
    have hinv' : ∀ i ≤ m, ∀ (t : T), ∀ x ∈ S' i, t • x ∈ S' i := by
      rintro i hi t _ ⟨u, hu, rfl⟩
      exact ⟨t • u, hinv (i + 1) (by omega) t u hu, rfl⟩
    have hcent' : ∀ i < m, ∀ x ∈ S' (i + 1), ∀ g : U ⧸ S 1, x⁻¹ * g⁻¹ * x * g ∈ S' i := by
      rintro i hi _ ⟨u, hu, rfl⟩ g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      exact (hmemS' i (by omega) _).2 (hcent (i + 1) (by omega) u hu g)
    have hsq' : ∀ i < m, ∀ x ∈ S' (i + 1), x ^ 2 ∈ S' i := by
      rintro i hi _ ⟨u, hu, rfl⟩
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow]
      exact (hmemS' i (by omega) _).2 (hsq (i + 1) (by omega) u hu)
    have hfix' : ∀ i < m, ∀ x ∈ S' (i + 1), (∀ t : T, (t • x)⁻¹ * x ∈ S' i) → x ∈ S' i := by
      rintro i hi _ ⟨u, hu, rfl⟩ hfu
      refine (hmemS' i (by omega) u).2 (hfix (i + 1) (by omega) u hu fun t => ?_)
      exact (hmemS' i (by omega) _).1 (hfu t)
    set Zs' : ι → Set (U ⧸ S 1) := fun k => (fun u : U => (u : U ⧸ S 1)) '' Zs k with hZs'
    set Ys' : ι → Set (U ⧸ S 1) := fun k => (fun u : U => (u : U ⧸ S 1)) '' Ys k with hYs'
    have hbil' : ∀ i < m, ∀ j < m, ∀ b : U ⧸ S 1 → U ⧸ S 1 → ZMod 2,
        (∀ x ∈ S' (i + 1), ∀ x' ∈ S' (i + 1), ∀ y ∈ S' (j + 1),
          b (x * x') y = b x y + b x' y) →
        (∀ x ∈ S' (i + 1), ∀ y ∈ S' (j + 1), ∀ y' ∈ S' (j + 1),
          b x (y * y') = b x y + b x y') →
        (∀ x ∈ S' i, ∀ y ∈ S' (j + 1), b x y = 0) →
        (∀ x ∈ S' (i + 1), ∀ y ∈ S' j, b x y = 0) →
        (∀ (t : T), ∀ x ∈ S' (i + 1), ∀ y ∈ S' (j + 1), b (t • x) (t • y) = b x y) →
        (∀ k, ∀ z ∈ Zs' k, ∀ y ∈ Ys' k, b z y = 0) →
        ∀ x ∈ S' (i + 1), ∀ y ∈ S' (j + 1), b x y = 0 := by
      intro i hi j hj b h1 h2 h3 h4 h5 h6
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      refine hbil (i + 1) (by omega) (j + 1) (by omega) (fun x y => b x y) ?_ ?_ ?_ ?_ ?_ ?_
        u hu v hv
      · intro x hx x' hx' y hy
        exact h1 _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ _ ⟨y, hy, rfl⟩
      · intro x hx y hy y' hy'
        exact h2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
      · intro x hx y hy
        exact h3 _ ((hmemS' i (by omega) x).2 hx) _ ⟨y, hy, rfl⟩
      · intro x hx y hy
        exact h4 _ ⟨x, hx, rfl⟩ _ ((hmemS' j (by omega) y).2 hy)
      · intro t x hx y hy
        exact h5 t _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      · intro k z hz y hy
        exact h6 k _ ⟨z, hz, rfl⟩ _ ⟨y, hy, rfl⟩
    have hNZ : N ≤ (S 1).comap η := map_subtype_le D
    set η' : P ⧸ N →* U ⧸ S 1 := QuotientGroup.map N (S 1) η hNZ with hη'def
    have hη'mk : ∀ x : P, η' (x : P ⧸ N) = ((η x : U) : U ⧸ S 1) := fun x => rfl
    have hη' : Function.Surjective η' := by
      intro y
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨x, rfl⟩ := hη u
      exact ⟨x, rfl⟩
    have hker' : ∀ x : P, (x : P ⧸ N) ∈ η'.ker ↔ x ∈ A := by
      intro x
      rw [MonoidHom.mem_ker, hη'mk, QuotientGroup.eq_one_iff]
      rfl
    have hC' : η'.ker ≤ center (P ⧸ N) := by
      intro y hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hx := (hker' x).1 hy
      refine mem_center_iff.2 fun g => ?_
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hAcomm x hx g]
    have h2' : IsPGroup 2 η'.ker := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨k, hk⟩ := hA2 ⟨x, (hker' x).1 hy⟩
      refine ⟨k, Subtype.ext ?_⟩
      have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
    have hTC' : ∀ (t : T), ∀ c ∈ η'.ker, t • c = c := by
      intro t c hc
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
      have hx := (hker' x).1 hc
      rw [hsmulP, QuotientGroup.eq]
      have h := inv_mem (hgen t x hx)
      rwa [mul_inv_rev, inv_inv] at h
    have hequiv' : ∀ (t : T) (y : P ⧸ N), η' (t • y) = t • η' y := by
      intro t y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hsmulP, hη'mk, hη'mk, hequiv, hsmulU]
    have hZY' : ∀ k, ∀ a y : P ⧸ N, η' a ∈ Zs' k → η' y ∈ Ys' k → a * y = y * a := by
      intro k a y ha hy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hη'mk] at ha hy
      obtain ⟨z, hz, hza⟩ := ha
      obtain ⟨w, hw, hwy⟩ := hy
      have hza' : (lift z)⁻¹ * a ∈ A := by
        rw [mem_comap, map_mul, map_inv, hlift]
        exact QuotientGroup.eq.1 hza
      have hwy' : (lift w)⁻¹ * y ∈ A := by
        rw [mem_comap, map_mul, map_inv, hlift]
        exact QuotientGroup.eq.1 hwy
      have hc : Commute (lift z) (lift w) :=
        hZY k _ _ (by rw [hlift]; exact hz) (by rw [hlift]; exact hw)
      have hc' : Commute (lift z * ((lift z)⁻¹ * a)) (lift w * ((lift w)⁻¹ * y)) :=
        (hc.mul_right (hAcomm _ hwy' _).symm).mul_left (hAcomm _ hza' _)
      rw [mul_inv_cancel_left, mul_inv_cancel_left] at hc'
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc'.eq]
    obtain ⟨K', hK'inv, hK'n, hK'compl, -⟩ := ih (hU.to_quotient (S 1)) S' hS0' hSm' hmono'
      hinv' hcent' hsq' hfix' Zs' Ys' hbil' η' hη' hC' h2' hTC' hequiv' hZY'
    set K : Subgroup P := K'.comap (QuotientGroup.mk' N) with hKdef
    have hmemK : ∀ x : P, x ∈ K ↔ (x : P ⧸ N) ∈ K' := fun x => Iff.rfl
    have hdec : ∀ x : P, ∃ c ∈ η.ker, ∃ k ∈ K, x = c * k := by
      intro x
      have hx : (x : P ⧸ N) ∈ η'.ker ⊔ K' := by
        rw [hK'compl.sup_eq_top]
        exact mem_top _
      rw [← SetLike.mem_coe, normal_mul, Set.mem_mul] at hx
      obtain ⟨y, hy, k', hk', hyk⟩ := hx
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨c, hc, n, hn, rfl⟩ := hAdec a ((hker' a).1 hy)
      refine ⟨c, hc, c⁻¹ * x, ?_, by group⟩
      rw [hmemK]
      have hn1 : ((n : P) : P ⧸ N) = 1 := (QuotientGroup.eq_one_iff n).2 hn
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hyk, QuotientGroup.mk_mul, hn1,
        mul_one, inv_mul_cancel_left]
      exact hk'
    have hdisj : ∀ x ∈ η.ker, x ∈ K → x = 1 := by
      intro x hx hxK
      have h1 : (x : P ⧸ N) = 1 :=
        disjoint_def.1 hK'compl.disjoint ((hker' x).2 (hkerA hx)) ((hmemK x).1 hxK)
      exact hNC x ((QuotientGroup.eq_one_iff x).1 h1) hx
    refine ⟨K, fun t x hx => ?_, hK'n.comap _,
      ⟨disjoint_def.2 fun hx hxK => hdisj _ hx hxK, ?_⟩, ?_, ?_⟩
    · rw [hmemK, ← hsmulP]
      exact hK'inv t _ ((hmemK x).1 hx)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      obtain ⟨c, hc, k, hk, rfl⟩ := hdec x
      exact mul_mem (mem_sup_left hc) (mem_sup_right hk)
    · rw [injective_iff_map_eq_one]
      intro k hk
      exact Subtype.ext (hdisj k hk k.2)
    · intro u
      obtain ⟨x, rfl⟩ := hη u
      obtain ⟨c, hc, k, hk, rfl⟩ := hdec x
      refine ⟨⟨k, hk⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype, map_mul,
        (MonoidHom.mem_ker).1 hc, one_mul]

theorem lift_commute_of_form_eq_zero {G E T : Type*} [Group G] [Group E] (η : E →* G)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (τ : T → G)
    (A B : Subgroup G) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hform : ∀ b : G → G → ZMod 2,
      (∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, b (x * x') y = b x y + b x' y) →
      (∀ x ∈ A, ∀ y ∈ B, ∀ y' ∈ B, b x (y * y') = b x y + b x y') →
      (∀ t, ∀ x ∈ A, ∀ y ∈ B, b (τ t * x * (τ t)⁻¹) (τ t * y * (τ t)⁻¹) = b x y) →
      ∀ x ∈ A, ∀ y ∈ B, b x y = 0) :
    ∀ a y : E, η a ∈ A → η y ∈ B → a * y = y * a := by
  classical
  have hcen : ∀ c ∈ η.ker, ∀ g : E, c * g = g * c := fun c hc g =>
    ((mem_center_iff.1 (hC hc)) g).symm
  set lift := Function.surjInv hη with hliftdef
  have hlift : ∀ u, η (lift u) = u := Function.surjInv_eq hη
  have hcmC : ∀ a y : E, η a ∈ A → η y ∈ B → a⁻¹ * y⁻¹ * a * y ∈ η.ker := by
    intro a y ha hy
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutator_eq_one_of_mul_comm (hAB _ ha _ hy)
  have hcm2 : ∀ a y : E, η a ∈ A → η y ∈ B → (a⁻¹ * y⁻¹ * a * y) ^ 2 = 1 := by
    intro a y ha hy
    have hsq : a ^ 2 ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hA2 _ ha
    rw [sq, ← commutator_mul_left hcen (hcmC a y ha hy), ← sq]
    exact commutator_central_left hcen hsq
  have hcongr : ∀ a a' x x' : E, η a = η a' → η x = η x' →
      a⁻¹ * x⁻¹ * a * x = a'⁻¹ * x'⁻¹ * a' * x' := by
    intro a a' x x' ha hx
    have hca : a⁻¹ * a' ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ha, inv_mul_cancel]
    have hcx : x⁻¹ * x' ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel]
    have h1 : a' = a * (a⁻¹ * a') := by group
    have h2 : x' = x * (x⁻¹ * x') := by group
    rw [h1, h2, commutator_mul_central_left hcen hca, commutator_mul_central_right hcen hcx]
  have hA : ∀ u ∈ A, η (lift u) ∈ A := fun u hu => by rw [hlift]; exact hu
  have hB : ∀ u ∈ B, η (lift u) ∈ B := fun u hu => by rw [hlift]; exact hu
  intro a y ha hy
  by_contra hne
  have hw1 : a⁻¹ * y⁻¹ * a * y ≠ 1 := fun h => hne (mul_comm_of_commutator_eq_one h)
  obtain ⟨φ, hφ, hφw⟩ := exists_zmod_two_functional hcen (hcmC a y ha hy) (hcm2 a y ha hy) hw1
  let b : G → G → ZMod 2 := fun u v => φ ((lift u)⁻¹ * (lift v)⁻¹ * lift u * lift v)
  have hb : ∀ a' y' : E, b (η a') (η y') = φ (a'⁻¹ * y'⁻¹ * a' * y') := by
    intro a' y'
    change φ _ = φ _
    rw [hcongr (lift (η a')) a' (lift (η y')) y' (hlift _) (hlift _)]
  have key := hform b ?_ ?_ ?_ (η a) ha (η y) hy
  · exact hφw (by rw [← hb a y]; exact key)
  · intro x hx x' hx' v hv
    change φ _ = φ _ + φ _
    rw [hcongr (lift (x * x')) (lift x * lift x') (lift v) (lift v)
      (by rw [hlift, map_mul, hlift, hlift]) rfl,
      commutator_mul_left hcen (hcmC _ _ (hA x hx) (hB v hv))]
    exact hφ _ (hcmC _ _ (hA x hx) (hB v hv)) _ (hcmC _ _ (hA x' hx') (hB v hv))
      (hcm2 _ _ (hA x hx) (hB v hv)) (hcm2 _ _ (hA x' hx') (hB v hv))
  · intro x hx v hv v' hv'
    change φ _ = φ _ + φ _
    rw [hcongr (lift x) (lift x) (lift (v * v')) (lift v * lift v') rfl
      (by rw [hlift, map_mul, hlift, hlift]),
      commutator_mul_right hcen (hcmC _ _ (hA x hx) (hB v hv)),
      hφ _ (hcmC _ _ (hA x hx) (hB v' hv')) _ (hcmC _ _ (hA x hx) (hB v hv))
        (hcm2 _ _ (hA x hx) (hB v' hv')) (hcm2 _ _ (hA x hx) (hB v hv)), add_comm]
  · intro t x hx v hv
    change φ _ = φ _
    set ℓ := lift (τ t)
    rw [hcongr (lift (τ t * x * (τ t)⁻¹)) (ℓ * lift x * ℓ⁻¹) (lift (τ t * v * (τ t)⁻¹))
      (ℓ * lift v * ℓ⁻¹) (by rw [hlift, map_mul, map_mul, map_inv, hlift, hlift])
      (by rw [hlift, map_mul, map_mul, map_inv, hlift, hlift])]
    have e : (ℓ * lift x * ℓ⁻¹)⁻¹ * (ℓ * lift v * ℓ⁻¹)⁻¹ * (ℓ * lift x * ℓ⁻¹) *
        (ℓ * lift v * ℓ⁻¹) = ℓ * ((lift x)⁻¹ * (lift v)⁻¹ * lift x * lift v) * ℓ⁻¹ := by
      group
    rw [e, ← hcen _ (hcmC _ _ (hA x hx) (hB v hv)) ℓ, mul_inv_cancel_right]

end CFSG.LocalAnalysis.ComponentInitial
