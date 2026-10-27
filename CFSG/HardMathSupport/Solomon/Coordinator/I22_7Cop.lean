module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7CopA
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7CopB
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

theorem i227cop_pRank_map_le {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (f : G →* G') {T : Subgroup G} (hinj : ∀ x ∈ T, f x = 1 → x = 1) {p : ℕ} (hp : 1 < p) :
    CFSG.Open.pRank p (T.map f) ≤ CFSG.Open.pRank p T := by
  have heq : ∀ {x y : G}, x ∈ T → y ∈ T → f x = f y → x = y := by
    intro x y hx hy h
    have h1 : f (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    exact inv_mul_eq_one.mp (hinj _ (mul_mem (inv_mem hx) hy) h1)
  obtain ⟨E', hE'T, hE', hcard⟩ := CFSG.SectionRank.exists_pRank hp (T.map f)
  set E : Subgroup G := E'.comap f ⊓ T with hE
  have hET : E ≤ T := inf_le_right
  have hEmap : ∀ x ∈ E, f x ∈ E' := fun x hx => hx.1
  have hE'E : ∀ y ∈ E', ∃ x ∈ E, f x = y := by
    intro y hy
    obtain ⟨x, hxT, rfl⟩ := hE'T hy
    exact ⟨x, ⟨hy, hxT⟩, rfl⟩
  have hEab : CFSG.Open.IsElemAbelian p E := by
    have := hE'.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have h1 := mul_comm' (⟨f a, hEmap a a.2⟩ : E') ⟨f b, hEmap b b.2⟩
      have h2 : f ((a : G) * b) = f ((b : G) * a) := by
        rw [map_mul, map_mul]; exact congrArg Subtype.val h1
      exact Subtype.ext (heq (mul_mem (hET a.2) (hET b.2)) (mul_mem (hET b.2) (hET a.2)) h2)
    · have h1 := hE'.2 (f x) (hEmap x hx)
      rw [← map_pow] at h1
      exact hinj _ (pow_mem (hET hx) p) h1
  have hcardE : Nat.card E = Nat.card E' := by
    refine Nat.card_congr (Equiv.ofBijective (fun x : E => (⟨f x, hEmap x x.2⟩ : E')) ⟨?_, ?_⟩)
    · intro a b hab
      exact Subtype.ext (heq (hET a.2) (hET b.2) (congrArg Subtype.val hab))
    · intro y
      obtain ⟨x, hx, hxy⟩ := hE'E y y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact CFSG.SectionRank.le_pRank hp hET hEab (by rw [hcardE, hcard])

theorem i227_coprime_holds : I22_7Coprime := by
  intro K _ _ N _ hN P hP hrk hquot
  have h3 : 1 < 3 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : K →* K ⧸ N := QuotientGroup.mk' N with hπ
  have hPN : P ⊓ N = ⊥ := i227cop_inf_eq_bot hP hN
  have hinjP : ∀ {T : Subgroup K}, T ≤ P → ∀ x ∈ T, π x = 1 → x = 1 := by
    intro T hT x hx h1
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).1 h1
    have : x ∈ P ⊓ N := ⟨hT hx, hxN⟩
    rwa [hPN, Subgroup.mem_bot] at this
  have hNH : N ≤ weakCoreIn 3 P ⊤ := i227cop_normal_le_weakCore N hN P hrk
  have hQle : ∀ Q : Subgroup K, Q ≤ P → 2 ≤ CFSG.Open.pRank 3 Q →
      3 ≤ CFSG.Open.pRank 3 (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set K))) →
      (⊤ : Subgroup K) ⊓ Subgroup.normalizer (Q : Set K) ≤ weakCoreIn 3 P ⊤ := by
    intro Q h1 h2 h3
    unfold weakCoreIn
    exact le_iSup₂_of_le Q ⟨h1, h2, h3⟩ le_rfl
  have hH : weakCoreIn 3 (P.map π) ⊤ ≤ (weakCoreIn 3 P ⊤).map π := by
    refine iSup₂_le fun Qb hQb => ?_
    obtain ⟨hQP, hr1, hr2⟩ := hQb
    set Q : Subgroup K := P ⊓ Qb.comap π with hQ
    have hQP' : Q ≤ P := inf_le_left
    have hQmap : Q.map π = Qb := by
      ext y
      constructor
      · rintro ⟨x, ⟨_, hx2⟩, rfl⟩
        exact hx2
      · intro hy
        obtain ⟨x, hxP, rfl⟩ := hQP hy
        exact ⟨x, ⟨hxP, hy⟩, rfl⟩
    have hr1' : 2 ≤ CFSG.Open.pRank 3 Q := by
      have := i227cop_pRank_map_le π (hinjP hQP') h3
      rw [hQmap] at this
      omega
    have hTP : Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set K)) ≤ P := sup_le hQP' inf_le_left
    have hsub : Qb ⊔ (P.map π ⊓ Subgroup.centralizer (Qb : Set (K ⧸ N))) ≤
        (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set K))).map π := by
      refine sup_le (hQmap ▸ Subgroup.map_mono le_sup_left) ?_
      rintro _ ⟨⟨x, hxP, rfl⟩, hy⟩
      have hy' : π x ∈ Subgroup.centralizer (Qb : Set (K ⧸ N)) := hy
      refine ⟨x, Subgroup.mem_sup_right ⟨hxP, ?_⟩, rfl⟩
      show x ∈ Subgroup.centralizer (Q : Set K)
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqb : π q ∈ Qb := hQmap ▸ Subgroup.mem_map_of_mem π hq
      have hcomm : π q * π x = π x * π q := Subgroup.mem_centralizer_iff.1 hy' _ hqb
      have hc1 : π (q * x * q⁻¹ * x⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hcomm]
        group
      have hxP' : x ∈ P := hxP
      have hqP : q ∈ P := hQP' hq
      have hc2 : q * x * q⁻¹ * x⁻¹ ∈ P ⊓ N :=
        ⟨P.mul_mem (P.mul_mem (P.mul_mem hqP hxP') (P.inv_mem hqP)) (P.inv_mem hxP'),
          (QuotientGroup.eq_one_iff _).1 hc1⟩
      rw [hPN, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc2
      exact hc2
    have hr2' : 3 ≤ CFSG.Open.pRank 3 (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set K))) :=
      hr2.trans ((CFSG.SectionRank.pRank_mono h3 hsub).trans
        (i227cop_pRank_map_le π (hinjP hTP) h3))
    intro xb hxb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    have hxn : ∀ h : K ⧸ N, h ∈ Qb ↔ (x : K ⧸ N) * h * (x : K ⧸ N)⁻¹ ∈ Qb :=
      Subgroup.mem_normalizer_iff.1 hxb.2
    have hx' : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q ⊔ N := by
      intro q hq
      have hqb : π q ∈ Qb := hQmap ▸ Subgroup.mem_map_of_mem π hq
      have h1 : π (x * q * x⁻¹) ∈ Qb := by
        have := (hxn (π q)).1 hqb
        simpa [hπ] using this
      rw [← hQmap] at h1
      obtain ⟨q', hq', hqq⟩ := h1
      have h2 : q'⁻¹ * (x * q * x⁻¹) ∈ N := by
        refine (QuotientGroup.eq_one_iff _).1 ?_
        change π (q'⁻¹ * (x * q * x⁻¹)) = 1
        rw [map_mul, map_inv, hqq, inv_mul_cancel]
      have h3 : x * q * x⁻¹ = q' * (q'⁻¹ * (x * q * x⁻¹)) := by group
      rw [h3]
      exact Subgroup.mul_mem_sup hq' h2
    obtain ⟨y, hy, n, hn, rfl⟩ := i227cop_exists_normalizer_mul hN (hP.to_le hQP') x hx'
    have hyH : y ∈ weakCoreIn 3 P ⊤ := hQle Q hQP' hr1' hr2' ⟨Subgroup.mem_top _, hy⟩
    refine ⟨y, hyH, ?_⟩
    have hn1 : π n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    show π y = π (y * n)
    rw [map_mul, hn1, mul_one]
  intro k _
  have h1 : π k ∈ weakCoreIn 3 (P.map π) ⊤ := hquot (Subgroup.mem_top _)
  obtain ⟨h, hh, hhk⟩ := hH h1
  have h2 : h⁻¹ * k ∈ N := QuotientGroup.eq.1 hhk
  have h4 : k = h * (h⁻¹ * k) := by group
  rw [h4]
  exact mul_mem hh (hNH h2)

end CFSG.HardMathSupport.Solomon.Coordinator
