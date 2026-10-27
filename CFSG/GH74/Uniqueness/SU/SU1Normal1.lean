module

public import CFSG.GH74.Uniqueness.SU.SU1Normal0
public import CFSG.GH74.Uniqueness.SU.SU1MaxClassShape

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

variable {P : Type} [Group P] {p : ℕ}

structure NSetting (Q : Subgroup P) (a : P) : Prop where
  normalQ : Q.Normal
  normalA : (zpowers a).Normal
  le : zpowers a ≤ Q
  centralizer : ∀ g ∈ Q, g * a = a * g → g ∈ zpowers a

namespace NSetting

variable [Finite P] {Q : Subgroup P} {a : P}

theorem exists_conj_pow (h : NSetting Q a) (g : P) : ∃ u : ℕ, g * a * g⁻¹ = a ^ u := by
  have := h.normalA.conj_mem a (Subgroup.mem_zpowers a) g
  obtain ⟨u, hu⟩ := exists_pow_eq_of_mem_zpowers this
  exact ⟨u, hu.symm⟩

omit [Finite P] in
theorem conj_mul {g h : P} {u v : ℕ} (hg : g * a * g⁻¹ = a ^ u) (hh : h * a * h⁻¹ = a ^ v) :
    (g * h) * a * (g * h)⁻¹ = a ^ (u * v) := by
  have e : (g * h) * a * (g * h)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by group
  rw [e, hh, ← conj_pow, hg, ← pow_mul]

theorem conj_acts_same (h : NSetting Q a) {y : P} {u : ℕ} (hy : y * a * y⁻¹ = a ^ u) (g : P) :
    (g * y * g⁻¹) * a * (g * y * g⁻¹)⁻¹ = a ^ u := by
  obtain ⟨v, hv⟩ : ∃ v : ℕ, g⁻¹ * a * g = a ^ v := by
    have h1 := h.normalA.conj_mem a (Subgroup.mem_zpowers a) g⁻¹
    rw [inv_inv] at h1
    obtain ⟨v, hv⟩ := exists_pow_eq_of_mem_zpowers h1
    exact ⟨v, hv.symm⟩
  have hbv : (g * a * g⁻¹) ^ v = a := by
    rw [conj_pow, ← hv]
    group
  calc (g * y * g⁻¹) * a * (g * y * g⁻¹)⁻¹ = g * y * (g⁻¹ * a * g) * y⁻¹ * g⁻¹ := by group
    _ = g * (y * a ^ v * y⁻¹) * g⁻¹ := by rw [hv]; group
    _ = g * ((y * a * y⁻¹) ^ v) * g⁻¹ := by rw [conj_pow]
    _ = g * a ^ (u * v) * g⁻¹ := by rw [hy, ← pow_mul]
    _ = (g * a * g⁻¹) ^ (u * v) := by rw [conj_pow]
    _ = ((g * a * g⁻¹) ^ v) ^ u := by rw [← pow_mul, mul_comm]
    _ = a ^ u := by rw [hbv]

theorem conj_mem_coset (h : NSetting Q a) {y : P} (hyQ : y ∈ Q) (g : P) :
    ∃ c ∈ zpowers a, g * y * g⁻¹ = y * c := by
  obtain ⟨u, hu⟩ := h.exists_conj_pow y
  have hsame := h.conj_acts_same hu g
  have hwQ : g * y * g⁻¹ ∈ Q := h.normalQ.conj_mem y hyQ g
  have hd : y⁻¹ * (g * y * g⁻¹) ∈ zpowers a := by
    apply h.centralizer
    · exact Q.mul_mem (Q.inv_mem hyQ) hwQ
    · have hcomm : (y⁻¹ * (g * y * g⁻¹)) * a * (y⁻¹ * (g * y * g⁻¹))⁻¹ = a := by
        calc (y⁻¹ * (g * y * g⁻¹)) * a * (y⁻¹ * (g * y * g⁻¹))⁻¹
            = y⁻¹ * ((g * y * g⁻¹) * a * (g * y * g⁻¹)⁻¹) * y := by group
          _ = y⁻¹ * (y * a * y⁻¹) * y := by rw [hsame, hu]
          _ = a := by group
      calc (y⁻¹ * (g * y * g⁻¹)) * a
          = (y⁻¹ * (g * y * g⁻¹)) * a * (y⁻¹ * (g * y * g⁻¹))⁻¹ * (y⁻¹ * (g * y * g⁻¹)) := by
            group
        _ = a * (y⁻¹ * (g * y * g⁻¹)) := by rw [hcomm]
  exact ⟨y⁻¹ * (g * y * g⁻¹), hd, by group⟩

theorem normal_of_between (h : NSetting Q a) {X : Subgroup P} (hAX : zpowers a ≤ X)
    (hXQ : X ≤ Q) : X.Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨c, hc, hxc⟩ := h.conj_mem_coset (hXQ hx) g
  rw [hxc]
  exact X.mul_mem hx (hAX hc)

end NSetting

theorem abelian_sup_of_commute {A B : Subgroup P} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hAB hx
  obtain ⟨a', ha', b', hb', rfl⟩ := mem_sup_of_commute hAB hy
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [← hAB a' ha' b hb]
    _ = a * a' * (b * b') := by group
    _ = a' * a * (b' * b) := by rw [hA a ha a' ha', hB b hb b' hb']
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [hAB a ha b' hb']
    _ = a' * b' * (a * b) := by group

variable [Finite P]

theorem exists_setting (hp : p.Prime) (hP : IsPGroup p P) {Q : Subgroup P} [hQ : Q.Normal]
    (hstar : ∀ E : Subgroup P, E.Normal → E ≤ Q → Open.IsElemAbelian p E →
      Nat.card E = p ^ 2 → False)
    (hrank : ∃ E : Subgroup P, E ≤ Q ∧ Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2) :
    ∃ (a : P) (k : ℕ), NSetting Q a ∧ orderOf a = p ^ k ∧ 1 ≤ k ∧ zpowers a ≠ Q := by
  have := Fact.mk hp
  obtain ⟨A, hAQ, hAn, hAab, hAmax⟩ := exists_maximal_normal_abelian Q
  have hC : ∀ g ∈ Q, (∀ x ∈ A, g * x = x * g) → g ∈ A := by
    intro g hgQ hgA
    by_contra hgnA
    set C : Subgroup P := centralizer (A : Set P) ⊓ Q with hCdef
    have hAC : A ≤ C := fun x hx =>
      ⟨Subgroup.mem_centralizer_iff.mpr (fun h hh => hAab h hh x hx), hAQ hx⟩
    have hgC : g ∈ C :=
      ⟨Subgroup.mem_centralizer_iff.mpr (fun h hh => (hgA h hh).symm), hgQ⟩
    have hCn : C.Normal := by
      refine ⟨fun c hc g' => ⟨?_, hQ.conj_mem c hc.2 g'⟩⟩
      refine Subgroup.mem_centralizer_iff.mpr (fun h hh => ?_)
      have h1 : g'⁻¹ * h * g' ∈ A := hAn.conj_mem h hh g'⁻¹ |> fun x => by simpa using x
      have h2 := Subgroup.mem_centralizer_iff.mp hc.1 _ h1
      calc h * (g' * c * g'⁻¹) = g' * ((g'⁻¹ * h * g') * c) * g'⁻¹ := by group
        _ = g' * (c * (g'⁻¹ * h * g')) * g'⁻¹ := by rw [h2]
        _ = g' * c * g'⁻¹ * h := by group
    have hlt : A < C := lt_of_le_of_ne hAC (fun h => hgnA (h ▸ hgC))
    obtain ⟨c, hcC, hcA, hcc⟩ := exists_central_mod hp hP hlt
    set B : Subgroup P := A ⊔ zpowers c with hB
    have hBQ : B ≤ Q := sup_le hAQ (Subgroup.zpowers_le.mpr hcC.2)
    have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
      refine abelian_sup_of_commute hAab ?_ ?_
      · rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
        exact ((Commute.refl c).zpow_zpow m n).eq
      · rintro x hx y ⟨m, rfl⟩
        have hcx : x * c = c * x := Subgroup.mem_centralizer_iff.mp hcC.1 x hx
        exact (Commute.zpow_right (show Commute x c from hcx) m).eq
    have hBn : B.Normal := by
      have hle : ∀ g' : P, B.map (MulAut.conj g').toMonoidHom ≤ B := by
        intro g'
        rw [hB, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨x, hx, rfl⟩
          exact Subgroup.mem_sup_left (hAn.conj_mem x hx g')
        · rintro _ ⟨x, hx, rfl⟩
          obtain ⟨m, rfl⟩ := hx
          change g' * c ^ m * g'⁻¹ ∈ B
          have : g' * c ^ m * g'⁻¹ = (g' * c * g'⁻¹) ^ m := by rw [conj_zpow]
          rw [this]
          have h1 : g' * c * g'⁻¹ = (g' * c * g'⁻¹ * c⁻¹) * c := by group
          refine zpow_mem ?_ m
          rw [h1]
          exact B.mul_mem (Subgroup.mem_sup_left (hcc g')) (Subgroup.mem_sup_right
            (Subgroup.mem_zpowers c))
      exact ⟨fun x hx g' => hle g' ⟨x, hx, rfl⟩⟩
    have hAB : A < B := lt_of_le_of_ne le_sup_left (fun h => hcA (h ▸ Subgroup.mem_sup_right
      (Subgroup.mem_zpowers c)))
    have := hAmax B hBQ hBn hBab
    have := card_lt_of_lt hAB
    omega
  have hcyc : IsCyclic A := isCyclic_of_no_normal_Ep2 hp hP hAab
    (fun E hE hEA hEel hEc => hstar E hE (hEA.trans hAQ) hEel hEc)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  set a : P := (g : P) with ha_def
  have hzA : zpowers a = A := by
    refine le_antisymm (Subgroup.zpowers_le.mpr g.2) (fun m hm => ?_)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨m, hm⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hset : NSetting Q a := by
    refine ⟨hQ, hzA ▸ hAn, hzA ▸ hAQ, fun x hxQ hxa => ?_⟩
    rw [hzA]
    refine hC x hxQ (fun y hy => ?_)
    rw [← hzA] at hy
    obtain ⟨m, rfl⟩ := hy
    exact (Commute.zpow_right (show Commute x a from hxa) m).eq
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hP.to_subgroup A)
  have hord : orderOf a = p ^ k := by
    rw [← hk, ha_def, Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨E₀, hE₀Q, hE₀, hE₀c⟩ := hrank
  have hne : zpowers a ≠ Q := by
    intro hzQ
    have hE₀A : E₀ ≤ A := hzA ▸ hzQ ▸ hE₀Q
    set S : Subgroup A := E₀.subgroupOf A with hS
    obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := S)
    have hog : orderOf g₀ = Nat.card S := orderOf_eq_card_of_forall_mem_zpowers hg₀
    have hcardS : Nat.card S = Nat.card E₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀A).toEquiv
    have hg0p : g₀ ^ p = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact (isElemAbelian_iff.mp hE₀).2 _ (Subgroup.mem_subgroupOf.mp g₀.2)
    have hdvd : orderOf g₀ ∣ p := orderOf_dvd_of_pow_eq_one hg0p
    have hle := Nat.le_of_dvd hp.pos hdvd
    rw [hog, hcardS, hE₀c] at hle
    have : p < p ^ 2 := by
      have := hp.one_lt
      nlinarith
    omega
  have hk1 : 1 ≤ k := by
    by_contra hcon
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hord
    have hQle : Q ≤ zpowers a := fun x hxQ => hset.centralizer x hxQ (by rw [hord]; simp)
    have hE₀le : E₀ ≤ zpowers a := hE₀Q.trans hQle
    have : Nat.card E₀ ≤ Nat.card (zpowers a) := Subgroup.card_le_of_le hE₀le
    rw [Nat.card_zpowers, hord, orderOf_one, hE₀c] at this
    have h1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  exact ⟨a, k, hset, hord, hk1, hne⟩

theorem mem_center_of_normal_prime (hp : p.Prime) (hP : IsPGroup p P) {z : P} (hz1 : z ≠ 1)
    (hzp : z ^ p = 1) (hzn : (zpowers z).Normal) : z ∈ center P := by
  have := Fact.mk hp
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hne : zpowers z ≠ ⊥ := by
    intro h
    exact hz1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers z))
  obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal (H := zpowers z) hne)
  obtain ⟨hcz, hcC⟩ := Subgroup.mem_inf.mp hc
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hle : zpowers c ≤ zpowers z := Subgroup.zpowers_le.mpr hcz
  have hoz : orderOf z = p := orderOf_eq_prime hzp hz1
  have hcp : c ^ p = 1 := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzp, one_zpow]
  have hoc : orderOf c = p := orderOf_eq_prime hcp hc1'
  have heq : zpowers c = zpowers z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hoz, hoc])
  have hzc : z ∈ zpowers c := heq ▸ Subgroup.mem_zpowers z
  have hcen : zpowers c ≤ center P := Subgroup.zpowers_le.mpr hcC
  exact hcen hzc

theorem NSetting.normal_zpowers_pow {Q : Subgroup P} {a : P} (h : NSetting Q a) (m : ℕ) :
    (zpowers (a ^ m)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨w, hw⟩ := h.exists_conj_pow g
  have h1 : g * a ^ m * g⁻¹ = (a ^ m) ^ w := by
    rw [← conj_pow, hw, ← pow_mul, ← pow_mul, mul_comm]
  rw [← conj_zpow, h1]
  exact zpow_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) n

omit [Finite P] in
theorem conj_npow {y a : P} {u : ℕ} (hy : y * a * y⁻¹ = a ^ u) (n : ℕ) :
    y ^ n * a * (y ^ n)⁻¹ = a ^ (u ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc y ^ (n + 1) * a * (y ^ (n + 1))⁻¹ = y ^ n * (y * a * y⁻¹) * (y ^ n)⁻¹ := by
          rw [pow_succ]; group
      _ = y ^ n * a ^ u * (y ^ n)⁻¹ := by rw [hy]
      _ = (y ^ n * a * (y ^ n)⁻¹) ^ u := by rw [conj_pow]
      _ = a ^ (u ^ (n + 1)) := by rw [ih, ← pow_mul, pow_succ]

end CFSG.GH74.Uniqueness.SU.SU1
