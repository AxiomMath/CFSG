module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusQ
public import Mathlib.GroupTheory.NoncommCoprod
public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

open scoped commutatorElement

variable {G : Type} [Group G]

structure QFacts (F : Subgroup G) : Prop where
  gen3 : ∀ f ∈ F, ∃ x ∈ F, ∃ y ∈ F, ∃ z ∈ F, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ f = x * y * z
  center_sq : ∀ z ∈ F, (∀ g ∈ F, g * z = z * g) → z * z = 1
  two_mul : ∀ x ∈ F, ∀ y ∈ F, x ^ 4 = 1 → y ^ 4 = 1 → (x * y) ^ 4 = 1
  exp_dvd : ∀ q ∈ F, q ^ 12 = 1
  two_pow : ∀ q ∈ F, q ^ 8 = 1 → q ^ 4 = 1
  comm_two : ∀ x ∈ F, ∀ y ∈ F, ⁅x, y⁆ ^ 4 = 1
  noncentral_two : ∃ t ∈ F, ∃ h ∈ F, t ^ 4 = 1 ∧ h ^ 3 = 1 ∧
    ∃ g ∈ F, g * (t⁻¹ * (h⁻¹ * t * h)) ≠ (t⁻¹ * (h⁻¹ * t * h)) * g
  normal_dich : ∀ d ∈ F, (∃ g ∈ F, g * d ≠ d * g) → ∀ q ∈ F, q ^ 4 = 1 →
    ∃ a ∈ F, ∃ b ∈ F, q = ⁅d, a⁆ * ⁅d, b⁆
  nontriv3 : ∃ h ∈ F, h ≠ 1 ∧ h ^ 3 = 1
  outer3 : ∀ y : G, y ∈ normalizer (F : Set G) → y ^ 3 = 1 →
    ∃ h ∈ F, h ^ 3 = 1 ∧ ∀ f ∈ F, y * f * y⁻¹ = h * f * h⁻¹

theorem GoodQ.qFacts {Q : Type} [Group Q] (hQ : GoodQ Q) {F : Subgroup G} (e : ↥F ≃* Q) :
    QFacts F := by
  have hF : GoodQ ↥F := GoodQ.of_mulEquiv e.symm hQ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨x, y, z, hx, hy, hz, h⟩ := hF.gen3 ⟨f, hf⟩
    refine ⟨x, x.2, y, y.2, z, z.2, ?_, ?_, ?_, ?_⟩
    · simpa using congrArg Subtype.val hx
    · simpa using congrArg Subtype.val hy
    · simpa using congrArg Subtype.val hz
    · simpa using congrArg Subtype.val h
  · intro z hz hc
    have := hF.center_sq ⟨z, hz⟩ (fun g => Subtype.ext (hc g g.2))
    simpa using congrArg Subtype.val this
  · intro x hx y hy hx4 hy4
    have := hF.two_mul ⟨x, hx⟩ ⟨y, hy⟩ (Subtype.ext (by simpa using hx4))
      (Subtype.ext (by simpa using hy4))
    simpa using congrArg Subtype.val this
  · intro q hq
    have := hF.exp_dvd ⟨q, hq⟩
    simpa using congrArg Subtype.val this
  · intro q hq hq8
    have := hF.two_pow ⟨q, hq⟩ (Subtype.ext (by simpa using hq8))
    simpa using congrArg Subtype.val this
  · intro x hx y hy
    have := hF.comm_two ⟨x, hx⟩ ⟨y, hy⟩
    simpa [commutatorElement_def] using congrArg Subtype.val this
  · obtain ⟨t, k, ht, hk, g, hg⟩ := hF.noncentral_two
    refine ⟨t, t.2, k, k.2, ?_, ?_, g, g.2, fun hc => hg (Subtype.ext ?_)⟩
    · simpa using congrArg Subtype.val ht
    · simpa using congrArg Subtype.val hk
    · simpa using hc
  · intro d hd hne q hq hq4
    obtain ⟨g, hg, hgd⟩ := hne
    have := hF.normal_dich ⟨d, hd⟩ ⟨⟨g, hg⟩, fun hc => hgd (by simpa using congrArg Subtype.val hc)⟩
      ⟨q, hq⟩ (Subtype.ext (by simpa using hq4))
    obtain ⟨a, b, hab⟩ := this
    refine ⟨a, a.2, b, b.2, ?_⟩
    simpa [commutatorElement_def] using congrArg Subtype.val hab
  · obtain ⟨k, hk1, hk3⟩ := hF.nontriv3
    refine ⟨k, k.2, fun hc => hk1 (Subtype.ext (by simpa using hc)), ?_⟩
    simpa using congrArg Subtype.val hk3
  · intro y hy hy3
    set σ : MulAut ↥F := F.normalizerMonoidHom ⟨y, hy⟩ with hσ
    have hσ3 : σ ^ 3 = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨y, hy⟩ : normalizer (F : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
      rw [this, map_one]
    obtain ⟨k, hk3, hk⟩ := hF.outer3 σ hσ3
    refine ⟨k, k.2, by simpa using congrArg Subtype.val hk3, fun f hf => ?_⟩
    have := congrArg Subtype.val (hk ⟨f, hf⟩)
    simpa [hσ] using this

section Commuting

variable {F N : Subgroup G}

theorem commute_of_commutator_eq_bot (h : ⁅F, N⁆ = ⊥) {a b : G} (ha : a ∈ F) (hb : b ∈ N) :
    Commute a b :=
  (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp h) ha) b hb).symm

theorem commutator_comm_eq_bot (h : ⁅F, N⁆ = ⊥) : ⁅N, F⁆ = ⊥ := by
  rw [Subgroup.commutator_comm]
  exact h

noncomputable def prodHom (h : ⁅F, N⁆ = ⊥) : ↥F × ↥N →* G :=
  F.subtype.noncommCoprod N.subtype fun a b => commute_of_commutator_eq_bot h a.2 b.2

theorem prodHom_apply (h : ⁅F, N⁆ = ⊥) (p : ↥F × ↥N) : prodHom h p = (p.1 : G) * (p.2 : G) :=
  MonoidHom.noncommCoprod_apply _ _ _ p

theorem mem_sup_of_commutator_eq_bot (h : ⁅F, N⁆ = ⊥) {z : G} :
    z ∈ F ⊔ N ↔ ∃ f ∈ F, ∃ n ∈ N, f * n = z := by
  constructor
  · intro hz
    let P : Subgroup G :=
      { carrier := {x | ∃ f ∈ F, ∃ n ∈ N, f * n = x}
        mul_mem' := by
          rintro _ _ ⟨f, hf, n, hn, rfl⟩ ⟨f', hf', n', hn', rfl⟩
          refine ⟨f * f', F.mul_mem hf hf', n * n', N.mul_mem hn hn', ?_⟩
          have := (commute_of_commutator_eq_bot h hf' hn).symm.eq
          calc f * f' * (n * n') = f * (f' * n) * n' := by group
            _ = f * (n * f') * n' := by rw [this.symm]
            _ = f * n * (f' * n') := by group
        one_mem' := ⟨1, F.one_mem, 1, N.one_mem, one_mul 1⟩
        inv_mem' := by
          rintro _ ⟨f, hf, n, hn, rfl⟩
          refine ⟨f⁻¹, F.inv_mem hf, n⁻¹, N.inv_mem hn, ?_⟩
          have := (commute_of_commutator_eq_bot h hf hn).inv_inv.eq
          rw [mul_inv_rev]
          exact this }
    have hle : F ⊔ N ≤ P := sup_le (fun f hf => ⟨f, hf, 1, N.one_mem, mul_one f⟩)
      (fun n hn => ⟨1, F.one_mem, n, hn, one_mul n⟩)
    exact hle hz
  · rintro ⟨f, hf, n, hn, rfl⟩
    exact (F ⊔ N).mul_mem (mem_sup_left hf) (mem_sup_right hn)

theorem commutator_mul_mul (h : ⁅F, N⁆ = ⊥) {f f' n n' : G} (hf : f ∈ F) (hf' : f' ∈ F)
    (hn : n ∈ N) (hn' : n' ∈ N) : ⁅f * n, f' * n'⁆ = ⁅f, f'⁆ * ⁅n, n'⁆ := by
  have := map_commutatorElement (prodHom h) (⟨f, hf⟩, ⟨n, hn⟩) (⟨f', hf'⟩, ⟨n', hn'⟩)
  simpa [prodHom_apply, commutatorElement_def] using this.symm

theorem commutator_mem_of_normalizes {A B : Subgroup G} (hA : B ≤ normalizer (A : Set G))
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) : ⁅a, b⁆ ∈ A := by
  have h1 : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
  rw [h1]
  exact A.mul_mem ha ((mem_normalizer_iff.mp (hA hb) a⁻¹).mp (A.inv_mem ha))

end Commuting

section Family

theorem commutator_mem_self {H : Subgroup G} {x y : G} (hx : x ∈ H) (hy : y ∈ H) : ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

@[expose] def PComm (S : Finset (Subgroup G)) : Prop :=
  (S : Set (Subgroup G)).Pairwise fun A B => ⁅A, B⁆ = ⊥

theorem PComm.mono {S T : Finset (Subgroup G)} (h : PComm T) (hST : S ⊆ T) : PComm S :=
  Set.Pairwise.mono (by exact_mod_cast hST) h

theorem commutator_sup_eq_bot {F : Subgroup G} {S : Finset (Subgroup G)}
    (hc : ∀ A ∈ S, ⁅F, A⁆ = ⊥) : ⁅F, S.sup id⁆ = ⊥ := by
  rw [Subgroup.commutator_comm, commutator_eq_bot_iff_le_centralizer]
  exact Finset.sup_le fun A hA => commutator_eq_bot_iff_le_centralizer.mp
    (commutator_comm_eq_bot (hc A hA))

theorem commProd_induction (R P : Subgroup G → Prop) (hbot : P ⊥)
    (hstep : ∀ F N : Subgroup G, QFacts F → R F → ⁅F, N⁆ = ⊥ → P N → P (F ⊔ N))
    (S : Finset (Subgroup G)) (hQ : ∀ A ∈ S, QFacts A) (hR : ∀ A ∈ S, R A) (hc : PComm S) :
    P (S.sup id) := by
  classical
  revert hQ hR hc
  induction S using Finset.induction_on with
  | empty => intro _ _ _; simpa using hbot
  | insert F S hF ih =>
    intro hQ hR hc
    rw [Finset.sup_insert]
    refine hstep F (S.sup id) (hQ F (Finset.mem_insert_self _ _))
      (hR F (Finset.mem_insert_self _ _)) ?_
      (ih (fun A hA => hQ A (Finset.mem_insert_of_mem hA))
        (fun A hA => hR A (Finset.mem_insert_of_mem hA)) (hc.mono (Finset.subset_insert _ _)))
    refine commutator_sup_eq_bot fun A hA => ?_
    have hne : F ≠ A := fun h => hF (h ▸ hA)
    exact hc (by simp) (by simp [hA]) hne

variable {S : Finset (Subgroup G)}

theorem center_sq_of_commProd (hQ : ∀ A ∈ S, QFacts A) (hc : PComm S) :
    ∀ z ∈ S.sup id, (∀ n ∈ S.sup id, n * z = z * n) → z * z = 1 := by
  refine commProd_induction (fun _ => True)
    (fun N => ∀ z ∈ N, (∀ n ∈ N, n * z = z * n) → z * z = 1) ?_ ?_ S hQ (fun _ _ => trivial) hc
  · intro z hz _
    rw [Subgroup.mem_bot] at hz
    subst hz
    simp
  · intro F N hF _ hFN ihN z hz hzc
    obtain ⟨f, hf, n, hn, rfl⟩ := (mem_sup_of_commutator_eq_bot hFN).mp hz
    have hfn : ∀ a ∈ F, ∀ b ∈ N, Commute a b := fun a ha b hb =>
      commute_of_commutator_eq_bot hFN ha hb
    have hf_c : ∀ g ∈ F, g * f = f * g := by
      intro g hg
      have : g * f * n = f * g * n := by
        calc g * f * n = g * (f * n) := by rw [mul_assoc]
          _ = f * n * g := hzc g (mem_sup_left hg)
          _ = f * (n * g) := by rw [mul_assoc]
          _ = f * (g * n) := by rw [(hfn g hg n hn).eq]
          _ = f * g * n := by rw [mul_assoc]
      exact mul_right_cancel this
    have hn_c : ∀ m ∈ N, m * n = n * m := by
      intro m hm
      have : f * (m * n) = f * (n * m) := by
        calc f * (m * n) = (f * m) * n := by rw [mul_assoc]
          _ = (m * f) * n := by rw [(hfn f hf m hm).eq]
          _ = m * (f * n) := by rw [mul_assoc]
          _ = f * n * m := hzc m (mem_sup_right hm)
          _ = f * (n * m) := by rw [mul_assoc]
      exact mul_left_cancel this
    have h1 := hF.center_sq f hf hf_c
    have h2 := ihN n hn hn_c
    calc f * n * (f * n) = f * (n * f) * n := by group
      _ = f * (f * n) * n := by rw [← (hfn f hf n hn).eq]
      _ = f * f * (n * n) := by group
      _ = 1 := by rw [h1, h2, mul_one]

theorem comm_two_of_commProd (hQ : ∀ A ∈ S, QFacts A) (hc : PComm S) :
    ∀ x ∈ S.sup id, ∀ y ∈ S.sup id, ⁅x, y⁆ ^ 4 = 1 := by
  refine commProd_induction (fun _ => True)
    (fun N => ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ^ 4 = 1) ?_ ?_ S hQ (fun _ _ => trivial) hc
  · intro x hx y hy
    rw [Subgroup.mem_bot] at hx hy
    subst hx
    subst hy
    simp
  · intro F N hF _ hFN ihN x hx y hy
    obtain ⟨f, hf, n, hn, rfl⟩ := (mem_sup_of_commutator_eq_bot hFN).mp hx
    obtain ⟨f', hf', n', hn', rfl⟩ := (mem_sup_of_commutator_eq_bot hFN).mp hy
    rw [commutator_mul_mul hFN hf hf' hn hn']
    have hcm : Commute ⁅f, f'⁆ ⁅n, n'⁆ :=
      commute_of_commutator_eq_bot hFN (commutator_mem_self hf hf') (commutator_mem_self hn hn')
    rw [hcm.mul_pow, hF.comm_two f hf f' hf', ihN n hn n' hn', one_mul]

variable {H : Subgroup G}

theorem two_mem_of_commProd (hQ : ∀ A ∈ S, QFacts A) (hc : PComm S)
    (hH : ∀ A ∈ S, ∀ f ∈ A, f ^ 4 = 1 → f ∈ H) :
    ∀ x ∈ S.sup id, x ^ 4 = 1 → x ∈ H := by
  refine commProd_induction (fun A => ∀ f ∈ A, f ^ 4 = 1 → f ∈ H)
    (fun N => ∀ x ∈ N, x ^ 4 = 1 → x ∈ H) ?_ ?_ S hQ hH hc
  · intro x hx _
    rw [Subgroup.mem_bot] at hx
    subst hx
    exact H.one_mem
  · intro F N hF hRF hFN ihN x hx hx4
    obtain ⟨f, hf, n, hn, rfl⟩ := (mem_sup_of_commutator_eq_bot hFN).mp hx
    have hcm : Commute f n := commute_of_commutator_eq_bot hFN hf hn
    rw [hcm.mul_pow] at hx4
    have hfN : f ^ 4 ∈ N := by
      have : f ^ 4 = (n ^ 4)⁻¹ := eq_inv_of_mul_eq_one_left hx4
      rw [this]
      exact N.inv_mem (N.pow_mem hn 4)
    have hcen : ∀ g ∈ F, g * f ^ 4 = f ^ 4 * g := fun g hg =>
      (commute_of_commutator_eq_bot hFN hg hfN).eq
    have hsq := hF.center_sq (f ^ 4) (F.pow_mem hf 4) hcen
    have hf8 : f ^ 8 = 1 := by
      calc f ^ 8 = f ^ 4 * f ^ 4 := by rw [← pow_add]
        _ = 1 := hsq
    have hf4 : f ^ 4 = 1 := hF.two_pow f hf hf8
    have hn4 : n ^ 4 = 1 := by simpa [hf4] using hx4
    exact H.mul_mem (hRF f hf hf4) (ihN n hn hn4)

theorem le_of_three_of_commProd (hQ : ∀ A ∈ S, QFacts A) (hc : PComm S)
    (hH : ∀ x ∈ S.sup id, x ^ 3 = 1 → x ∈ H) : S.sup id ≤ H := by
  have key : ∀ T : Finset (Subgroup G), (∀ A ∈ T, QFacts A) → PComm T →
      (∀ x ∈ T.sup id, x ^ 3 = 1 → x ∈ H) → T.sup id ≤ H := by
    intro T hT hTc hTH
    refine commProd_induction (fun _ => True)
      (fun N => (∀ x ∈ N, x ^ 3 = 1 → x ∈ H) → N ≤ H) ?_ ?_ T hT (fun _ _ => trivial) hTc hTH
    · intro _
      simp
    · intro F N hF _ hFN ihN hall
      refine sup_le ?_ (ihN fun x hx hx3 => hall x (mem_sup_right hx) hx3)
      intro f hf
      obtain ⟨x, hx, y, hy, z, hz, hx3, hy3, hz3, rfl⟩ := hF.gen3 f hf
      exact H.mul_mem (H.mul_mem (hall x (mem_sup_left hx) hx3) (hall y (mem_sup_left hy) hy3))
        (hall z (mem_sup_left hz) hz3)
  exact key S hQ hc hH

end Family

section Unique

theorem sup_le_normalizer_of_mem {S : Finset (Subgroup G)} (hc : PComm S) {F : Subgroup G}
    (hF : F ∈ S) : S.sup id ≤ normalizer (F : Set G) := by
  refine Finset.sup_le fun A hA => ?_
  by_cases h : A = F
  · subst h
    exact Subgroup.le_normalizer
  · exact (commutator_eq_bot_iff_le_centralizer.mp
      (hc (Finset.mem_coe.mpr hA) (Finset.mem_coe.mpr hF) h)).trans (centralizer_le_normalizer _)

theorem le_sup_of_mem {S : Finset (Subgroup G)} {F : Subgroup G} (hF : F ∈ S) : F ≤ S.sup id :=
  Finset.le_sup (f := id) hF

theorem commute_of_inf_central {F T : Subgroup G} (hF : QFacts F)
    (hFT : F ≤ normalizer (T : Set G)) (hTF : T ≤ normalizer (F : Set G))
    (hcen : ∀ d ∈ F ⊓ T, ∀ g ∈ F, g * d = d * g) : ∀ t ∈ T, ∀ f ∈ F, t * f = f * t := by
  have h3 : ∀ t ∈ T, ∀ f ∈ F, f ^ 3 = 1 → t * f = f * t := by
    intro t ht f hf hf3
    have hcF : ⁅t, f⁆ ∈ F := by
      have : t * f * t⁻¹ ∈ F := (mem_normalizer_iff.mp (hTF ht) f).mp hf
      rw [commutatorElement_def]
      exact F.mul_mem this (F.inv_mem hf)
    have hcT : ⁅t, f⁆ ∈ T := by
      have h1 : f * t⁻¹ * f⁻¹ ∈ T := (mem_normalizer_iff.mp (hFT hf) t⁻¹).mp (T.inv_mem ht)
      have : ⁅t, f⁆ = t * (f * t⁻¹ * f⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact T.mul_mem ht h1
    have hcc : ∀ g ∈ F, g * ⁅t, f⁆ = ⁅t, f⁆ * g := hcen _ ⟨hcF, hcT⟩
    have hcomm : Commute ⁅t, f⁆ f := (hcc f hf).symm
    have hconj : ⁅t, f⁆ * f = t * f * t⁻¹ := by rw [commutatorElement_def]; group
    have hc3 : ⁅t, f⁆ ^ 3 = 1 := by
      have h1 : (t * f * t⁻¹) ^ 3 = 1 := by rw [conj_pow, hf3]; group
      rw [← hconj, hcomm.mul_pow, hf3, mul_one] at h1
      exact h1
    have hc2 := hF.center_sq _ hcF hcc
    have hc1 : ⁅t, f⁆ = 1 := by
      calc ⁅t, f⁆ = ⁅t, f⁆ * ⁅t, f⁆ * ⁅t, f⁆ := by rw [hc2, one_mul]
        _ = ⁅t, f⁆ ^ 3 := (pow_three' _).symm
        _ = 1 := hc3
    exact commutatorElement_eq_one_iff_mul_comm.mp hc1
  intro t ht f hf
  obtain ⟨x, hx, y, hy, z, hz, hx3, hy3, hz3, rfl⟩ := hF.gen3 f hf
  have := ((Commute.mul_right (Commute.mul_right (h3 t ht x hx hx3) (h3 t ht y hy hy3)))
    (h3 t ht z hz hz3))
  exact this

@[expose] def twoSet (F : Subgroup G) : Set G := {x | x ∈ F ∧ x ^ 4 = 1}

theorem ncard_twoSet_eq {F T : Subgroup G} (e : ↥F ≃* ↥T) :
    (twoSet F).ncard = (twoSet T).ncard := by
  refine Set.ncard_congr (fun x hx => ((e ⟨x, hx.1⟩ : ↥T) : G)) ?_ ?_ ?_
  · intro a ha
    refine ⟨(e ⟨a, ha.1⟩).2, ?_⟩
    have h1 : (⟨a, ha.1⟩ : ↥F) ^ 4 = 1 := Subtype.ext (by simpa using ha.2)
    have : (e ⟨a, ha.1⟩) ^ 4 = 1 := by rw [← map_pow, h1, map_one]
    simpa using congrArg Subtype.val this
  · intro a b ha hb hab
    have := e.injective (Subtype.ext hab)
    simpa using congrArg Subtype.val this
  · intro b hb
    refine ⟨((e.symm ⟨b, hb.1⟩ : ↥F) : G), ⟨(e.symm ⟨b, hb.1⟩).2, ?_⟩, ?_⟩
    · have h1 : (⟨b, hb.1⟩ : ↥T) ^ 4 = 1 := Subtype.ext (by simpa using hb.2)
      have : (e.symm ⟨b, hb.1⟩) ^ 4 = 1 := by rw [← map_pow, h1, map_one]
      simpa using congrArg Subtype.val this
    · simp

theorem mem_of_normal_isomorphic [Finite G] {Q : Type} [Group Q] (hQ : GoodQ Q)
    {S : Finset (Subgroup G)} (hS : ∀ F ∈ S, Nonempty (↥F ≃* Q)) (hc : PComm S)
    {T : Subgroup G} (hT : Nonempty (↥T ≃* Q)) (hTN : T ≤ S.sup id)
    (hn : S.sup id ≤ normalizer (T : Set G)) : T ∈ S := by
  classical
  have hQF : ∀ F ∈ S, QFacts F := fun F hF => hQ.qFacts (hS F hF).some
  have hTF : QFacts T := hQ.qFacts hT.some
  have hFT : ∀ F ∈ S, F ≤ normalizer (T : Set G) := fun F hF => (le_sup_of_mem hF).trans hn
  have hTnF : ∀ F ∈ S, T ≤ normalizer (F : Set G) := fun F hF =>
    hTN.trans (sup_le_normalizer_of_mem hc hF)
  have hdich : ∀ F ∈ S, (∀ t ∈ T, ∀ f ∈ F, t * f = f * t) ∨ twoSet F ⊆ T := by
    intro F hF
    by_cases h : ∀ d ∈ F ⊓ T, ∀ g ∈ F, g * d = d * g
    · exact Or.inl (commute_of_inf_central (hQF F hF) (hFT F hF) (hTnF F hF) h)
    · right
      push Not at h
      obtain ⟨d, hd, g, hg, hne⟩ := h
      intro q hq
      obtain ⟨a, ha, b, hb, hqab⟩ := (hQF F hF).normal_dich d hd.1 ⟨g, hg, hne⟩ q hq.1 hq.2
      rw [hqab]
      exact T.mul_mem (commutator_mem_of_normalizes (hFT F hF) hd.2 ha)
        (commutator_mem_of_normalizes (hFT F hF) hd.2 hb)
  have hex : ∃ F ∈ S, twoSet F ⊆ T := by
    by_contra hne
    push Not at hne
    have hTc : ∀ F ∈ S, ∀ t ∈ T, ∀ f ∈ F, t * f = f * t := fun F hF =>
      (hdich F hF).resolve_right (hne F hF)
    have hTN' : S.sup id ≤ centralizer (T : Set G) := Finset.sup_le fun F hF f hf => by
      rw [mem_centralizer_iff]
      intro t ht
      exact hTc F hF t ht f hf
    obtain ⟨t, ht, k, hk, _, _, g, hg, hgne⟩ := hTF.noncentral_two
    apply hgne
    have hw : t⁻¹ * (k⁻¹ * t * k) ∈ T :=
      T.mul_mem (T.inv_mem ht) (T.mul_mem (T.mul_mem (T.inv_mem hk) ht) hk)
    exact (mem_centralizer_iff.mp (hTN' (hTN hw))) g hg
  have huniq : ∀ F₁ ∈ S, ∀ F₂ ∈ S, twoSet F₁ ⊆ T → twoSet F₂ ⊆ T → F₁ = F₂ := by
    intro F₁ h₁ F₂ h₂ s₁ s₂
    by_contra hne
    have e1 : (twoSet F₁).ncard = (twoSet T).ncard :=
      ncard_twoSet_eq ((hS F₁ h₁).some.trans hT.some.symm)
    have e2 : (twoSet F₂).ncard = (twoSet T).ncard :=
      ncard_twoSet_eq ((hS F₂ h₂).some.trans hT.some.symm)
    have u1 : twoSet F₁ = twoSet T :=
      Set.eq_of_subset_of_ncard_le (fun x hx => ⟨s₁ hx, hx.2⟩) e1.symm.le
    have u2 : twoSet F₂ = twoSet T :=
      Set.eq_of_subset_of_ncard_le (fun x hx => ⟨s₂ hx, hx.2⟩) e2.symm.le
    obtain ⟨t, ht, k, hk, _, _, g, hg, hgne⟩ := (hQF F₁ h₁).noncentral_two
    have hw : t⁻¹ * (k⁻¹ * t * k) ∈ twoSet F₁ := by
      refine ⟨F₁.mul_mem (F₁.inv_mem ht) (F₁.mul_mem (F₁.mul_mem (F₁.inv_mem hk) ht) hk), ?_⟩
      have := (hQF F₁ h₁).comm_two t⁻¹ (F₁.inv_mem ht) k⁻¹ (F₁.inv_mem hk)
      simpa [commutatorElement_def, mul_assoc] using this
    have hw2 : t⁻¹ * (k⁻¹ * t * k) ∈ F₂ := (u1.trans u2.symm ▸ hw : _ ∈ twoSet F₂).1
    exact hgne (commute_of_commutator_eq_bot (hc (Finset.mem_coe.mpr h₁)
      (Finset.mem_coe.mpr h₂) hne) hg hw2).eq
  obtain ⟨F₀, hF₀, hsub⟩ := hex
  have hcomm_other : ∀ F ∈ S, F ≠ F₀ → ∀ t ∈ T, ∀ f ∈ F, t * f = f * t := fun F hF hne =>
    (hdich F hF).resolve_right fun hs => hne (huniq F hF F₀ hF₀ hs hsub)
  have hsplit : S.sup id = F₀ ⊔ (S.erase F₀).sup id := by
    conv_lhs => rw [← Finset.insert_erase hF₀]
    rw [Finset.sup_insert]
    rfl
  have hFR : ⁅F₀, (S.erase F₀).sup id⁆ = ⊥ := commutator_sup_eq_bot fun A hA =>
    hc (Finset.mem_coe.mpr hF₀) (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hA))
      (Finset.ne_of_mem_erase hA).symm
  have hTR : ∀ t ∈ T, ∀ r ∈ (S.erase F₀).sup id, t * r = r * t := by
    have hle : (S.erase F₀).sup id ≤ centralizer (T : Set G) :=
      Finset.sup_le fun A hA a ha => by
        rw [mem_centralizer_iff]
        intro t ht
        exact hcomm_other A (Finset.mem_of_mem_erase hA) (Finset.ne_of_mem_erase hA) t ht a ha
    intro t ht r hr
    exact (mem_centralizer_iff.mp (hle hr)) t ht
  have h3T : ∀ t ∈ T, t ^ 3 = 1 → t ∈ F₀ := by
    intro t ht ht3
    obtain ⟨f, hf, r, hr, rfl⟩ := (mem_sup_of_commutator_eq_bot hFR).mp (hsplit ▸ hTN ht)
    have hfr : Commute f r := commute_of_commutator_eq_bot hFR hf hr
    have hrc : ∀ m ∈ (S.erase F₀).sup id, m * r = r * m := by
      intro m hm
      have hfm : Commute f m := commute_of_commutator_eq_bot hFR hf hm
      have h1 := hTR _ ht m hm
      have : m * r = r * m := by
        have hr' : r = f⁻¹ * (f * r) := by group
        calc m * r = m * (f⁻¹ * (f * r)) := by rw [← hr']
          _ = f⁻¹ * (m * (f * r)) := by rw [← mul_assoc, ← mul_assoc, hfm.inv_left.symm.eq]; group
          _ = f⁻¹ * ((f * r) * m) := by rw [← h1]
          _ = r * m := by group
      exact this
    have hsq := center_sq_of_commProd (S := S.erase F₀)
      (fun A hA => hQF A (Finset.mem_of_mem_erase hA))
      (hc.mono (Finset.erase_subset _ _)) r hr hrc
    have hr3 : r ^ 3 = r := by
      calc r ^ 3 = r * r * r := pow_three' r
        _ = r := by rw [hsq, one_mul]
    have : f ^ 3 * r = 1 := by
      have := ht3
      rwa [hfr.mul_pow, hr3] at this
    have hrF : r ∈ F₀ := by
      have : r = (f ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right this
      rw [this]
      exact F₀.inv_mem (F₀.pow_mem hf 3)
    exact F₀.mul_mem hf hrF
  have hTle : T ≤ F₀ := by
    intro t ht
    obtain ⟨x, hx, y, hy, z, hz, hx3, hy3, hz3, rfl⟩ := hTF.gen3 t ht
    exact F₀.mul_mem (F₀.mul_mem (h3T x hx hx3) (h3T y hy hy3)) (h3T z hz hz3)
  have hcard : Nat.card ↥F₀ ≤ Nat.card ↥T :=
    (Nat.card_congr ((hS F₀ hF₀).some.trans hT.some.symm).toEquiv).le
  have : T = F₀ := Subgroup.eq_of_le_of_card_ge hTle hcard
  exact this ▸ hF₀

theorem map_mem_of_map_eq [Finite G] {Q : Type} [Group Q] (hQ : GoodQ Q)
    {S : Finset (Subgroup G)} (hS : ∀ F ∈ S, Nonempty (↥F ≃* Q)) (hc : PComm S)
    (φ : G ≃* G) (hφ : (S.sup id).map φ.toMonoidHom = S.sup id) {F : Subgroup G} (hF : F ∈ S) :
    F.map φ.toMonoidHom ∈ S := by
  refine mem_of_normal_isomorphic hQ hS hc ?_ ?_ ?_
  · exact ⟨(Subgroup.equivMapOfInjective F φ.toMonoidHom φ.injective).symm.trans
      (hS F hF).some⟩
  · rw [← hφ]
    exact Subgroup.map_mono (le_sup_of_mem hF)
  · intro x hx
    have hx' : φ.symm x ∈ S.sup id := by
      have : x ∈ (S.sup id).map φ.toMonoidHom := by rw [hφ]; exact hx
      obtain ⟨y, hy, rfl⟩ := this
      simpa using hy
    have hnorm := sup_le_normalizer_of_mem hc hF hx'
    apply mem_normalizer_of_map_conj_eq
    have key : (F.map φ.toMonoidHom).map (MulAut.conj x).toMonoidHom =
        (F.map (MulAut.conj (φ.symm x)).toMonoidHom).map φ.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext y
      simp [MulAut.conj_apply]
    rw [key, map_conj_eq_of_mem_normalizer hnorm]

end Unique

end CFSG.OddStandard.Solomon75
