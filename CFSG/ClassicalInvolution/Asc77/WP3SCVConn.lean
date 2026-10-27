module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Asc77.SCV

open CFSG CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

section Quasisimple

variable {G : Type*} [Group G]

theorem isQuasisimple_normal_le_center_or_eq_top (h : CFSG.Open.IsQuasisimple G) (N : Subgroup G)
    [N.Normal] : N ≤ Subgroup.center G ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple⟩ := h
  have hnorm : (N.map (QuotientGroup.mk' (Subgroup.center G))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (G ⧸ Subgroup.center G) _ hsimple
    (N.map (QuotientGroup.mk' (Subgroup.center G))) hnorm with h0 | h1
  · left
    intro n hn
    have : QuotientGroup.mk' (Subgroup.center G) n ∈ (⊥ : Subgroup (G ⧸ Subgroup.center G)) := by
      rw [← h0]
      exact ⟨n, hn, rfl⟩
    simpa using this
  · right
    have hcov : ∀ g : G, ∃ c ∈ Subgroup.center G,
        (QuotientGroup.mk g : G ⧸ N) = QuotientGroup.mk c := by
      intro g
      have hg : QuotientGroup.mk' (Subgroup.center G) g ∈
          N.map (QuotientGroup.mk' (Subgroup.center G)) := by rw [h1]; trivial
      obtain ⟨n, hn, hng⟩ := hg
      have hc : n⁻¹ * g ∈ Subgroup.center G := by
        have : (QuotientGroup.mk' (Subgroup.center G)) (n⁻¹ * g) = 1 := by
          rw [map_mul, map_inv, hng, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff _).mp this
      refine ⟨n⁻¹ * g, hc, ?_⟩
      rw [QuotientGroup.eq]
      have := ‹N.Normal›.conj_mem n⁻¹ (N.inv_mem hn) g⁻¹
      simpa [mul_assoc] using this
    have hcomm : IsMulCommutative (G ⧸ N) := by
      refine ⟨⟨fun x y => ?_⟩⟩
      induction x using QuotientGroup.induction_on with | _ a => ?_
      induction y using QuotientGroup.induction_on with | _ b => ?_
      obtain ⟨c, hc, hca⟩ := hcov a
      obtain ⟨d, hd, hdb⟩ := hcov b
      rw [hca, hdb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        (Subgroup.mem_center_iff.mp hd) c]
    have hle : commutator G ≤ N :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
    rw [hperf] at hle
    exact top_le_iff.mp hle

end Quasisimple

section Family

variable {K : Type*} [Group K]

@[expose] def Partners (Φ : Set (Subgroup K)) (R : Subgroup K) : Set (Subgroup K) :=
  {S | S ∈ Φ ∧ S ≠ R ∧ Commutes R S}

structure ClosedFamily (Φ : Set (Subgroup K)) : Prop where
  conj : ∀ (g : K) (R : Subgroup K), R ∈ Φ → conjSub g R ∈ Φ
  qs : ∀ R ∈ Φ, CFSG.Open.IsQuasisimple ↥R

variable {Φ : Set (Subgroup K)}

theorem ClosedFamily.perfect (hΦ : ClosedFamily Φ) {R : Subgroup K} (hR : R ∈ Φ) : ⁅R, R⁆ = R :=
  Subgroup.commutator_eq_self (H := R)
    (hH := Group.isPerfect_def.mpr (hΦ.qs R hR).1)

theorem ClosedFamily.nonab (hΦ : ClosedFamily Φ) {R : Subgroup K} (hR : R ∈ Φ) :
    ¬ Commutes R R := by
  intro h
  obtain ⟨-, hsimple⟩ := hΦ.qs R hR
  have hc : Subgroup.center ↥R = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (h y.1 y.2 x.1 x.2)
  have : Subsingleton (↥R ⧸ Subgroup.center ↥R) := by
    rw [hc]
    exact QuotientGroup.subsingleton_quotient_top
  exact (not_nontrivial_iff_subsingleton.mpr this) hsimple.toNontrivial

theorem ClosedFamily.simple (hΦ : ClosedFamily Φ) {R : Subgroup K} (hR : R ∈ Φ)
    (N : Subgroup K) (hNR : N ≤ R) (hnorm : ∀ x ∈ R, ∀ n ∈ N, x * n * x⁻¹ ∈ N) :
    (∀ n ∈ N, ∀ x ∈ R, x * n = n * x) ∨ N = R := by
  have hN : (N.subgroupOf R).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm g.1 g.2 n.1 hn
  rcases isQuasisimple_normal_le_center_or_eq_top (hΦ.qs R hR) (N.subgroupOf R) with h | h
  · left
    intro n hn x hx
    have hn' : (⟨n, hNR hn⟩ : ↥R) ∈ N.subgroupOf R := Subgroup.mem_subgroupOf.mpr hn
    have := (Subgroup.mem_center_iff.mp (h hn')) ⟨x, hx⟩
    exact congrArg Subtype.val this
  · right
    refine le_antisymm hNR fun x hx => ?_
    have : (⟨x, hx⟩ : ↥R) ∈ N.subgroupOf R := by rw [h]; trivial
    exact Subgroup.mem_subgroupOf.mp this

theorem fix_partner (hΦ : ClosedFamily Φ) {R A B : Subgroup K}
    (hb : ∃ a b : Subgroup K, ∀ S ∈ Partners Φ R, S = a ∨ S = b)
    (hA : A ∈ Partners Φ R) (hB : B ∈ Partners Φ R) (hAB : A ≠ B) {x : K} (hx : x ∈ A) :
    conjSub x B = B := by
  obtain ⟨a₀, b₀, hab⟩ := hb
  have hRA : Commutes A R := hA.2.2.symm
  have hxR : conjSub x R = R := conjSub_eq_of_mem_of_commutes hx hRA
  have hmem : conjSub x B ∈ Partners Φ R := by
    refine ⟨hΦ.conj x B hB.1, ?_, ?_⟩
    · intro h
      apply hB.2.1
      calc B = conjSub x⁻¹ (conjSub x B) := (conjSub_inv_conjSub x B).symm
        _ = conjSub x⁻¹ R := by rw [h]
        _ = R := conjSub_eq_of_mem_of_commutes (A.inv_mem hx) hRA
    · have := hB.2.2.conjSub x
      rwa [hxR] at this
  have hsub : ∀ S ∈ Partners Φ R, S = A ∨ S = B := by
    intro S hS
    rcases hab A hA with hA' | hA' <;> rcases hab B hB with hB' | hB' <;>
      rcases hab S hS with hS' | hS' <;>
      first
        | exact absurd (hA'.trans hB'.symm) hAB
        | exact Or.inl (hS'.trans hA'.symm)
        | exact Or.inr (hS'.trans hB'.symm)
  rcases hsub _ hmem with h | h
  · exfalso
    apply hAB
    have h2 : conjSub x A = A := conjSub_eq_self_of_mem hx
    exact (conjSub_injective x (h.trans h2.symm)).symm
  · exact h

theorem partner_triangle (hΦ : ClosedFamily Φ) {R A B : Subgroup K}
    (hb : ∃ a b : Subgroup K, ∀ S ∈ Partners Φ R, S = a ∨ S = b)
    (hA : A ∈ Partners Φ R) (hB : B ∈ Partners Φ R) (hAB : A ≠ B) : Commutes A B := by
  have hxA : ∀ x ∈ A, conjSub x B = B := fun x hx => fix_partner hΦ hb hA hB hAB hx
  have hxB : ∀ y ∈ B, conjSub y A = A := fun y hy => fix_partner hΦ hb hB hA hAB.symm hy
  have hnA : ∀ x ∈ A, ∀ b ∈ B, x * b * x⁻¹ ∈ B := by
    intro x hx b hb'
    have := conj_mem_conjSub (n := x) hb'
    rwa [hxA x hx] at this
  have hnB : ∀ y ∈ B, ∀ a ∈ A, y * a * y⁻¹ ∈ A := by
    intro y hy a ha
    have := conj_mem_conjSub (n := y) ha
    rwa [hxB y hy] at this
  have hIA : ∀ n ∈ A ⊓ B, ∀ x ∈ A, x * n = n * x := by
    rcases hΦ.simple hA.1 (A ⊓ B) inf_le_left
      (fun x hx n hn => ⟨A.mul_mem (A.mul_mem hx hn.1) (A.inv_mem hx), hnA x hx n hn.2⟩) with h | h
    · exact h
    · exfalso
      have hle : A ≤ B := h ▸ inf_le_right
      rcases hΦ.simple hB.1 A hle (fun y hy a ha => hnB y hy a ha) with h' | h'
      · exact hΦ.nonab hA.1 (fun x hx y hy => h' y hy x (hle hx))
      · exact hAB h'
  have hIB : ∀ n ∈ A ⊓ B, ∀ x ∈ B, x * n = n * x := by
    rcases hΦ.simple hB.1 (A ⊓ B) inf_le_right
      (fun y hy n hn => ⟨hnB y hy n hn.1, B.mul_mem (B.mul_mem hy hn.2) (B.inv_mem hy)⟩) with h | h
    · exact h
    · exfalso
      have hle : B ≤ A := h ▸ inf_le_left
      rcases hΦ.simple hA.1 B hle (fun x hx b hb' => hnA x hx b hb') with h' | h'
      · exact hΦ.nonab hB.1 (fun x hx y hy => h' y hy x (hle hx))
      · exact hAB h'.symm
  have hcomm_le : ⁅A, B⁆ ≤ A ⊓ B := by
    rw [Subgroup.commutator_le]
    intro a ha b hb'
    refine ⟨?_, ?_⟩
    · have h1 : b * a⁻¹ * b⁻¹ ∈ A := hnB b hb' a⁻¹ (A.inv_mem ha)
      have h2 := A.mul_mem ha h1
      simpa [commutatorElement_def, mul_assoc] using h2
    · have h1 : a * b * a⁻¹ ∈ B := hnA a ha b hb'
      have h2 := B.mul_mem h1 (B.inv_mem hb')
      simpa [commutatorElement_def, mul_assoc] using h2
  have h1 : ⁅⁅A, B⁆, A⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro g hg a ha
    have := hIA g (hcomm_le hg) a ha
    exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr this.symm)
  have h2 : ⁅⁅B, A⁆, A⁆ = ⊥ := by rw [Subgroup.commutator_comm B A]; exact h1
  have h3 : ⁅⁅A, A⁆, B⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hΦ.perfect hA.1] at h3
  intro x hx y hy
  have : ⁅x, y⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h3] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp this)

theorem partner_component (hΦ : ClosedFamily Φ)
    (hb : ∀ R ∈ Φ, ∃ a b : Subgroup K, ∀ S ∈ Partners Φ R, S = a ∨ S = b)
    {R : Subgroup K} (hR : R ∈ Φ) {X Y : Subgroup K} (hX : X = R ∨ X ∈ Partners Φ R)
    (hY : Y ∈ Partners Φ X) : Y = R ∨ Y ∈ Partners Φ R := by
  rcases hX with rfl | hX
  · exact Or.inr hY
  · by_cases hYR : Y = R
    · exact Or.inl hYR
    · right
      have hXΦ : X ∈ Φ := hX.1
      have hRX : R ∈ Partners Φ X := ⟨hR, fun h => hX.2.1 h.symm, hX.2.2.symm⟩
      have hc : Commutes R Y := partner_triangle hΦ (hb X hXΦ) hRX hY (Ne.symm hYR)
      exact ⟨hY.1, hYR, hc⟩

theorem partner_reach (hΦ : ClosedFamily Φ)
    (hb : ∀ R ∈ Φ, ∃ a b : Subgroup K, ∀ S ∈ Partners Φ R, S = a ∨ S = b)
    (hconn : ∀ A ∈ Φ, ∀ B ∈ Φ,
      Relation.ReflTransGen (fun U V : Subgroup K => U ∈ Φ ∧ V ∈ Φ ∧ Commutes U V) A B)
    {R S : Subgroup K} (hR : R ∈ Φ) (hS : S ∈ Φ) : S = R ∨ S ∈ Partners Φ R := by
  have key : ∀ Y : Subgroup K,
      Relation.ReflTransGen (fun U V : Subgroup K => U ∈ Φ ∧ V ∈ Φ ∧ Commutes U V) R Y →
        Y = R ∨ Y ∈ Partners Φ R := by
    intro Y h
    induction h with
    | refl => exact Or.inl rfl
    | @tail X Y' _ hstep ih =>
      obtain ⟨hXΦ, hYΦ, hc⟩ := hstep
      have hYX : Y' ≠ X := by
        intro h
        subst h
        exact hΦ.nonab hYΦ hc
      exact partner_component hΦ hb hR ih ⟨hYΦ, hYX, hc⟩
  exact key S (hconn R hR S hS)

theorem false_of_three_partners {R S₁ S₂ S₃ : Subgroup K}
    (hb : ∃ a b : Subgroup K, ∀ S ∈ Partners Φ R, S = a ∨ S = b)
    (h₁ : S₁ ∈ Partners Φ R) (h₂ : S₂ ∈ Partners Φ R) (h₃ : S₃ ∈ Partners Φ R)
    (h12 : S₁ ≠ S₂) (h13 : S₁ ≠ S₃) (h23 : S₂ ≠ S₃) : False := by
  obtain ⟨a, b, hab⟩ := hb
  rcases hab S₁ h₁ with e1 | e1 <;> rcases hab S₂ h₂ with e2 | e2 <;>
    rcases hab S₃ h₃ with e3 | e3 <;>
    first
      | exact h12 (e1.trans e2.symm)
      | exact h13 (e1.trans e3.symm)
      | exact h23 (e2.trans e3.symm)

def actEquiv (hΦ : ClosedFamily Φ) (g : K) : Equiv.Perm ↥Φ where
  toFun R := ⟨conjSub g R.1, hΦ.conj g R.1 R.2⟩
  invFun R := ⟨conjSub g⁻¹ R.1, hΦ.conj g⁻¹ R.1 R.2⟩
  left_inv R := Subtype.ext (conjSub_inv_conjSub g R.1)
  right_inv R := Subtype.ext (conjSub_conjSub_inv g R.1)

def actHom (hΦ : ClosedFamily Φ) : K →* Equiv.Perm ↥Φ where
  toFun := actEquiv hΦ
  map_one' := Equiv.ext fun R => Subtype.ext (conjSub_one R.1)
  map_mul' g h := Equiv.ext fun R => Subtype.ext (conjSub_mul g h R.1)

theorem false_of_connected (hΦ : ClosedFamily Φ)
    (hb : ∀ R ∈ Φ, ∃ a b : Subgroup K, ∀ S ∈ Partners Φ R, S = a ∨ S = b)
    (hconn : ∀ A ∈ Φ, ∀ B ∈ Φ,
      Relation.ReflTransGen (fun U V : Subgroup K => U ∈ Φ ∧ V ∈ Φ ∧ Commutes U V) A B)
    {R : Subgroup K} (hR : R ∈ Φ) (hK : CFSG.Open.IsQuasisimple K) (htop : R ≠ ⊤) : False := by
  obtain ⟨a, b, hab⟩ := hb R hR
  have hsub : Φ ⊆ {R, a, b} := by
    intro S hS
    rcases partner_reach hΦ hb hconn hR hS with h | h
    · exact Or.inl h
    · rcases hab S h with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  have hfin : Finite ↥Φ := (Set.toFinite {R, a, b}).subset hsub |>.to_subtype
  have hcard : Nat.card ↥Φ ≤ 4 := by
    have h1 : Nat.card ↥Φ ≤ Nat.card ↥({R, a, b} : Set (Subgroup K)) :=
      Nat.card_mono (Set.toFinite _) hsub
    have h2 : Nat.card ↥({R, a, b} : Set (Subgroup K)) ≤ 3 := by
      rw [Nat.card_coe_set_eq]
      calc ({R, a, b} : Set (Subgroup K)).ncard
          ≤ ({a, b} : Set (Subgroup K)).ncard + 1 := Set.ncard_insert_le _ _
        _ ≤ (({b} : Set (Subgroup K)).ncard + 1) + 1 := by
            have := Set.ncard_insert_le a ({b} : Set (Subgroup K))
            omega
        _ = 3 := by simp
    omega
  have hsolv : Group.IsSolvable (Equiv.Perm ↥Φ) := Equiv.Perm.isSolvable hcard
  have hperfK : Group.IsPerfect K := Group.isPerfect_def.mpr hK.1
  have hperfR : Group.IsPerfect (actHom hΦ).range := Group.IsPerfect.range (actHom hΦ)
  have htriv : (actHom hΦ).range = ⊥ := by
    by_contra hne
    have : Nontrivial (actHom hΦ).range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable (G := (actHom hΦ).range) inferInstance
  have hfix : ∀ g : K, conjSub g R = R := by
    intro g
    have : actHom hΦ g = 1 := by
      have : actHom hΦ g ∈ (actHom hΦ).range := ⟨g, rfl⟩
      rw [htriv] at this
      exact Subgroup.mem_bot.mp this
    have h2 := congrArg Subtype.val (DFunLike.congr_fun this ⟨R, hR⟩)
    exact h2
  have hnormal : R.Normal := ⟨fun n hn g => by
    have := conj_mem_conjSub (n := g) hn
    rwa [hfix g] at this⟩
  rcases isQuasisimple_normal_le_center_or_eq_top hK R with h | h
  · exact hΦ.nonab hR (fun x hx y hy => (Subgroup.mem_center_iff.mp (h hy) x))
  · exact htop h

end Family

end CFSG.ClassicalInvolution.Asc77.SCV
