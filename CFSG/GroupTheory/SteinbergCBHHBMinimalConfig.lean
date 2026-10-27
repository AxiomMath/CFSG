module

public import CFSG.GroupTheory.SteinbergBKMinimalCoprimeClassTwo

public noncomputable section

namespace CFSG.GroupTheory.HallHigmanB

open Subgroup

section Norm

theorem eq_one_of_fixed_of_comm {X : Type*} [Group X] [Finite X] (hX : ∀ a b : X, a * b = b * a)
    (φ : X →* X) {r : ℕ} (hφr : ∀ a, (⇑φ)^[r] a = a) (hcop : Nat.Coprime r (Nat.card X))
    (hgen : ∀ a : X, a ∈ closure {c | ∃ b : X, ∃ i : ℕ, c = b⁻¹ * (⇑φ)^[i] b}) {a : X}
    (ha : φ a = a) : a = 1 := by
  classical
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hX }
  let N : X →* X :=
    { toFun := fun b => ∏ i ∈ Finset.range r, (⇑φ)^[i] b
      map_one' := by simp [iterate_map_one]
      map_mul' := fun b c => by simp [iterate_map_mul, Finset.prod_mul_distrib] }
  have hNφ : ∀ b, N (φ b) = N b := by
    intro b
    change ∏ i ∈ Finset.range r, (⇑φ)^[i] (φ b) = ∏ i ∈ Finset.range r, (⇑φ)^[i] b
    have h1 : ∀ i, (⇑φ)^[i] (φ b) = (⇑φ)^[i + 1] b := fun i => by
      rw [Function.iterate_succ_apply]
    simp only [h1]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · rw [hr]
      simp
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Finset.prod_range_succ (fun x => (⇑φ)^[x + 1] b), Finset.prod_range_succ'
      (fun i => (⇑φ)^[i] b), hφr b, Function.iterate_zero_apply]
  have hNφi : ∀ i b, N ((⇑φ)^[i] b) = N b := by
    intro i
    induction i with
    | zero => intro b; rfl
    | succ i ih => intro b; rw [Function.iterate_succ_apply', hNφ, ih]
  have hle : closure {c | ∃ b : X, ∃ i : ℕ, c = b⁻¹ * (⇑φ)^[i] b} ≤ N.ker := by
    rw [closure_le]
    rintro _ ⟨b, i, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hNφi, inv_mul_cancel]
  have hNa : N a = a ^ r := by
    change ∏ i ∈ Finset.range r, (⇑φ)^[i] a = a ^ r
    have h1 : ∀ i, (⇑φ)^[i] a = a := fun i => Function.iterate_fixed ha i
    simp [h1]
  have hapow : a ^ r = 1 := by
    rw [← hNa]
    exact MonoidHom.mem_ker.1 (hle (hgen a))
  have h1 : orderOf a ∣ r := orderOf_dvd_of_pow_eq_one hapow
  have h2 : orderOf a ∣ Nat.card X := orderOf_dvd_natCard a
  have h3 : orderOf a = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  exact orderOf_eq_one_iff.1 h3

end Norm

section Conj

variable {Γ : Type*} [Group Γ]

theorem conj_mem_of_mem_normalizer {Q : Subgroup Γ} {u : Γ}
    (hu : u ∈ normalizer (Q : Set Γ)) {g : Γ} (hg : g ∈ Q) : u * g * u⁻¹ ∈ Q :=
  (mem_normalizer_iff.1 hu g).1 hg

@[expose, instance_reducible] def conjZpowers (Q : Subgroup Γ) (x : Γ)
    (hx : x ∈ normalizer (Q : Set Γ)) : MulDistribMulAction (zpowers x) Q where
  smul u g := ⟨u * g * (u : Γ)⁻¹, conj_mem_of_mem_normalizer (zpowers_le.2 hx u.2) g.2⟩
  one_smul g := Subtype.ext (by
    change ((1 : zpowers x) : Γ) * g * ((1 : zpowers x) : Γ)⁻¹ = g
    simp)
  mul_smul u v g := Subtype.ext (by
    change ((u * v : zpowers x) : Γ) * g * ((u * v : zpowers x) : Γ)⁻¹ =
      (u : Γ) * ((v : Γ) * g * (v : Γ)⁻¹) * (u : Γ)⁻¹
    simp only [Subgroup.coe_mul]
    group)
  smul_mul u g h := Subtype.ext (by
    change (u : Γ) * ((g : Γ) * h) * (u : Γ)⁻¹ =
      ((u : Γ) * g * (u : Γ)⁻¹) * ((u : Γ) * h * (u : Γ)⁻¹)
    group)
  smul_one u := Subtype.ext (by
    change (u : Γ) * 1 * (u : Γ)⁻¹ = 1
    group)

end Conj

section Minimal

variable {Γ : Type*} [Group Γ]

theorem minimal_config {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hqp : q ≠ p)
    {Q : Subgroup Γ} [Finite Q] (hQq : IsPGroup q Q) {x : Γ}
    (hx : x ∈ normalizer (Q : Set Γ)) {n : ℕ} (hn : 1 ≤ n) (hxn : x ^ (p ^ n) = 1)
    (hz : ∃ g ∈ Q, x ^ (p ^ (n - 1)) * g ≠ g * x ^ (p ^ (n - 1)))
    (hmin : ∀ R : Subgroup Γ, R ≤ Q → R ≠ Q → x ∈ normalizer (R : Set Γ) →
      ∀ g ∈ R, x ^ (p ^ (n - 1)) * g = g * x ^ (p ^ (n - 1))) :
    (∀ s ∈ Q, ∀ t ∈ Q, ∀ g ∈ Q, (t * s * t⁻¹ * s⁻¹) * g = g * (t * s * t⁻¹ * s⁻¹)) ∧
    (∀ g ∈ Q, g ∈ closure {c | ∃ h ∈ Q, ∃ i : ℕ,
      c = h⁻¹ * ((x ^ (p ^ (n - 1))) ^ i * h * ((x ^ (p ^ (n - 1))) ^ i)⁻¹)}) ∧
    (∀ g ∈ Q, (∀ h ∈ Q, (x ^ (p ^ (n - 1)) * g * (x ^ (p ^ (n - 1)))⁻¹ * g⁻¹) * h =
        h * (x ^ (p ^ (n - 1)) * g * (x ^ (p ^ (n - 1)))⁻¹ * g⁻¹)) →
      ∀ h ∈ Q, g * h = h * g) := by
  classical
  set z := x ^ (p ^ (n - 1)) with hzdef
  have hzp : z ^ p = 1 := by
    rw [hzdef, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hn, hxn]
  have hxfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨p ^ n,
    pow_pos hp.out.pos n, hxn⟩
  have : Finite (zpowers x) := finite_zpowers.2 hxfin
  let _ := conjZpowers Q x hx
  have hsmul : ∀ (u : zpowers x) (g : Q), ((u • g : Q) : Γ) = (u : Γ) * g * (u : Γ)⁻¹ :=
    fun _ _ => rfl
  set zU : zpowers x := ⟨z, pow_mem (mem_zpowers x) _⟩ with hzUdef
  have hzUp : zU ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hzp)
  set X : Subgroup (zpowers x) := zpowers zU with hXdef
  have hXn : X.Normal := ⟨fun a _ u => by
    have h1 : u * a * u⁻¹ = a := by
      obtain ⟨i, hi⟩ := mem_zpowers_iff.1 u.2
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 a.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hi, ← hj, (Commute.zpow_zpow_self x i j).eq, mul_inv_cancel_right]
    rwa [h1]⟩
  have hXq : ¬ q ∣ Nat.card X := by
    intro h
    rw [hXdef, Nat.card_zpowers] at h
    have := h.trans (orderOf_dvd_of_pow_eq_one hzUp)
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 this)
  have hstab : ∀ g : Q, zU • g = g → ∀ u ∈ X, u • g = g := by
    intro g hg u hu
    have hzU : zU ∈ MulAction.stabilizer (zpowers x) g := hg
    exact (zpowers_le.2 hzU) hu
  have hnc : ∃ u ∈ X, ∃ g : Q, u • g ≠ g := by
    obtain ⟨g, hgQ, hg⟩ := hz
    refine ⟨zU, mem_zpowers zU, ⟨g, hgQ⟩, fun h => hg ?_⟩
    have h1 := congrArg Subtype.val h
    rw [hsmul] at h1
    change z * g * z⁻¹ = g at h1
    calc z * g = z * g * z⁻¹ * z := by group
      _ = g * z := by rw [h1]
  have hmin' : ∀ R : Subgroup Q, R ≠ ⊤ → (∀ u : zpowers x, ∀ r ∈ R, u • r ∈ R) →
      ∀ u ∈ X, ∀ r ∈ R, u • r = r := by
    intro R hR hRinv u hu r hr
    refine hstab r ?_ u hu
    set R' := R.map Q.subtype
    have hR'Q : R' ≤ Q := by
      rintro _ ⟨r, -, rfl⟩
      exact r.2
    have hR'ne : R' ≠ Q := by
      intro h
      apply hR
      rw [eq_top_iff]
      intro g _
      have : (g : Γ) ∈ R' := by rw [h]; exact g.2
      obtain ⟨g', hg', hgg'⟩ := this
      rwa [show g' = g from Subtype.ext hgg'] at hg'
    have hxR' : x ∈ normalizer (R' : Set Γ) := by
      rw [mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨r', hr', rfl⟩
        exact ⟨_, hRinv ⟨x, mem_zpowers x⟩ r' hr', rfl⟩
      · rintro ⟨r', hr', hr'h⟩
        refine ⟨_, hRinv ⟨x⁻¹, inv_mem (mem_zpowers x)⟩ r' hr', ?_⟩
        change x⁻¹ * (r' : Γ) * x⁻¹⁻¹ = h
        rw [show (r' : Γ) = x * h * x⁻¹ from hr'h]
        group
    have h1 := hmin R' hR'Q hR'ne hxR' r ⟨r, hr, rfl⟩
    apply Subtype.ext
    rw [hsmul]
    change z * r * z⁻¹ = r
    rw [h1, mul_inv_cancel_right]
  obtain ⟨hgen, hcomm⟩ := CFSG.GroupTheory.SteinbergBK.minimal_coprime_pgroup_action_class_two
    hQq X hXq hnc hmin'
  have hO1 : ∀ s ∈ Q, ∀ t ∈ Q, ∀ g ∈ Q,
      (t * s * t⁻¹ * s⁻¹) * g = g * (t * s * t⁻¹ * s⁻¹) := by
    intro s hs t ht g hg
    have hmem : (⟨t, ht⟩ : Q) * ⟨s, hs⟩ * (⟨t, ht⟩ : Q)⁻¹ * (⟨s, hs⟩ : Q)⁻¹ ∈ center Q := by
      apply hcomm
      rw [← commutatorElement_def]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    have := congrArg Subtype.val ((mem_center_iff.1 hmem) ⟨g, hg⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this.symm
  have hpowU : ∀ u ∈ X, ∃ i : ℕ, u = zU ^ i := by
    intro u hu
    have hfin : IsOfFinOrder zU := isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.out.pos, hzUp⟩
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).1
      (hfin.mem_powers_iff_mem_zpowers.2 hu)
    exact ⟨i, hi.symm⟩
  have hO2 : ∀ g ∈ Q, g ∈ closure {c | ∃ h ∈ Q, ∃ i : ℕ,
      c = h⁻¹ * (z ^ i * h * (z ^ i)⁻¹)} := by
    intro g hg
    have h1 : (⟨g, hg⟩ : Q) ∈ closure {g | ∃ q : Q, ∃ x' ∈ X, g = q⁻¹ * (x' • q)} := by
      rw [hgen]
      exact mem_top _
    have h2 := mem_map_of_mem Q.subtype h1
    rw [MonoidHom.map_closure] at h2
    refine closure_mono ?_ h2
    rintro _ ⟨_, ⟨q', x', hx', rfl⟩, rfl⟩
    obtain ⟨i, rfl⟩ := hpowU x' hx'
    refine ⟨q', q'.2, i, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hsmul, Subgroup.coe_pow]
  have hO3 : ∀ g ∈ Q, (∀ h ∈ Q, (z * g * z⁻¹ * g⁻¹) * h = h * (z * g * z⁻¹ * g⁻¹)) →
      ∀ h ∈ Q, g * h = h * g := by
    intro g hg hfix h hh
    set c := MulDistribMulAction.toMonoidHom Q zU with hcdef
    have hcZ : center Q ≤ (center Q).comap c := by
      intro a ha
      rw [mem_comap, mem_center_iff]
      intro b
      have hb : b = c (zU⁻¹ • b) := by
        rw [hcdef, MulDistribMulAction.toMonoidHom_apply, smul_inv_smul]
      rw [hb, ← map_mul, ← map_mul, (mem_center_iff.1 ha) (zU⁻¹ • b)]
    set φ := QuotientGroup.map (center Q) (center Q) c hcZ with hφdef
    have hφmk : ∀ g' : Q, φ (g' : Q ⧸ center Q) = ((zU • g' : Q) : Q ⧸ center Q) := fun g' => rfl
    have hφit : ∀ (i : ℕ) (g' : Q), (⇑φ)^[i] (g' : Q ⧸ center Q) =
        ((zU ^ i • g' : Q) : Q ⧸ center Q) := by
      intro i
      induction i with
      | zero => intro g'; simp
      | succ i ih =>
        intro g'
        rw [Function.iterate_succ_apply', ih, hφmk, pow_succ', mul_smul]
    have hXc : ∀ a b : Q ⧸ center Q, a * b = b * a := by
      intro a b
      induction a using QuotientGroup.induction_on with
      | H s =>
      induction b using QuotientGroup.induction_on with
      | H t =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_center_iff]
      intro k
      apply Subtype.ext
      have h1 := hO1 ((s : Γ)⁻¹) (inv_mem s.2) ((t : Γ)⁻¹) (inv_mem t.2) k k.2
      simp only [inv_inv] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
      rw [show (t : Γ)⁻¹ * (s : Γ)⁻¹ * ((t : Γ) * (s : Γ)) =
        (t : Γ)⁻¹ * (s : Γ)⁻¹ * (t : Γ) * (s : Γ) by group]
      exact h1.symm
    have hφr : ∀ a : Q ⧸ center Q, (⇑φ)^[p] a = a := by
      intro a
      induction a using QuotientGroup.induction_on with
      | H g' => rw [hφit, hzUp, one_smul]
    have hcop : Nat.Coprime p (Nat.card (Q ⧸ center Q)) := by
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (hQq.to_quotient (center Q))
      rw [ha]
      exact ((Nat.coprime_primes hp.out hq.out).2 hqp.symm).pow_right a
    have hgen' : ∀ a : Q ⧸ center Q, a ∈ closure {c | ∃ b : Q ⧸ center Q, ∃ i : ℕ,
        c = b⁻¹ * (⇑φ)^[i] b} := by
      intro a
      induction a using QuotientGroup.induction_on with
      | H g' =>
      have h1 : g' ∈ closure {g | ∃ q : Q, ∃ x' ∈ X, g = q⁻¹ * (x' • q)} := by
        rw [hgen]
        exact mem_top _
      have h2 := mem_map_of_mem (QuotientGroup.mk' (center Q)) h1
      rw [MonoidHom.map_closure] at h2
      refine closure_mono ?_ h2
      rintro _ ⟨_, ⟨q', x', hx', rfl⟩, rfl⟩
      obtain ⟨i, rfl⟩ := hpowU x' hx'
      refine ⟨(q' : Q ⧸ center Q), i, ?_⟩
      rw [hφit, map_mul, map_inv]
      rfl
    have hfixφ : φ ((⟨g, hg⟩ : Q) : Q ⧸ center Q) = ((⟨g, hg⟩ : Q) : Q ⧸ center Q) := by
      rw [hφmk, QuotientGroup.eq, mem_center_iff]
      intro k
      apply Subtype.ext
      have hck := hfix k k.2
      have hcg := hfix g hg
      set cc := z * g * z⁻¹ * g⁻¹ with hccdef
      have hw : ((zU • (⟨g, hg⟩ : Q) : Q) : Γ)⁻¹ * g = cc⁻¹ := by
        rw [hsmul]
        change (z * g * z⁻¹)⁻¹ * g = cc⁻¹
        have h1 : z * g * z⁻¹ = cc * g := by rw [hccdef]; group
        have h2 : cc⁻¹ * g = g * cc⁻¹ := by
          calc cc⁻¹ * g = cc⁻¹ * (g * cc) * cc⁻¹ := by group
            _ = cc⁻¹ * (cc * g) * cc⁻¹ := by rw [hcg]
            _ = g * cc⁻¹ := by group
        rw [h1, mul_inv_rev, mul_assoc, h2, ← mul_assoc, inv_mul_cancel, one_mul]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hw]
      calc (k : Γ) * cc⁻¹ = cc⁻¹ * (cc * k) * cc⁻¹ := by group
        _ = cc⁻¹ * (k * cc) * cc⁻¹ := by rw [hck]
        _ = cc⁻¹ * k := by group
    have hone := eq_one_of_fixed_of_comm hXc φ hφr hcop hgen' hfixφ
    have hgZ : (⟨g, hg⟩ : Q) ∈ center Q := (QuotientGroup.eq_one_iff _).1 hone
    have := congrArg Subtype.val ((mem_center_iff.1 hgZ) ⟨h, hh⟩)
    exact this.symm
  exact ⟨hO1, hO2, hO3⟩

end Minimal

end CFSG.GroupTheory.HallHigmanB
