module

public import CFSG.CGT.Timmesfeld75.Reduction
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral
public import CFSG.LocalAnalysis.ZStar
public import CFSG.GroupTheory.LocalCores.MinimalNormal
import CFSG.CGT.Timmesfeld75.Sec3Odd

public section

namespace CFSG.CGT.Timmesfeld75

open scoped commutatorElement Pointwise

structure Hyp213 {K : Type*} [Group K] (T : Subgroup K) : Prop where
  isWC : IsWC T
  four_le : 4 ≤ Nat.card T
  normalClosure_eq_top : Subgroup.normalClosure (T : Set K) = ⊤
  eq_bot_of_solvable : ∀ R : Subgroup K, R.Normal → Group.IsSolvable R → R = ⊥

section OddCore

variable {K : Type*} [Group K]

theorem odd_card_sup_of_le_normalizer {A B : Subgroup K}
    (hBA : B ≤ Subgroup.normalizer (A : Set K)) (hA : Odd (Nat.card A)) (hB : Odd (Nat.card B)) :
    Odd (Nat.card (A ⊔ B : Subgroup K)) := by
  rw [sup_comm]
  have := Subgroup.normal_subgroupOf_of_le_normalizer hBA
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBA
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A hBA
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (B ⊔ A)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : A ≤ B ⊔ A)).toEquiv]
  exact (Odd.of_dvd_nat hB (Subgroup.card_quotient_dvd_card _)).mul hA

theorem conjSubgroup_sup (g : K) (A B : Subgroup K) :
    conjSubgroup g (A ⊔ B) = conjSubgroup g A ⊔ conjSubgroup g B :=
  Subgroup.map_sup _ _ _

theorem le_normalizer_of_forall_conj {M R : Subgroup K} (h : ∀ m ∈ M, ∀ r ∈ R, m * r * m⁻¹ ∈ R) :
    M ≤ Subgroup.normalizer (R : Set K) := fun m hm =>
  Subgroup.mem_normalizer_iff.2 fun r =>
    ⟨h m hm r, fun hr => by simpa [mul_assoc] using h m⁻¹ (M.inv_mem hm) _ hr⟩

variable {T : Subgroup K}

theorem Hyp213.center_eq_bot (h : Hyp213 T) : Subgroup.center K = ⊥ :=
  h.eq_bot_of_solvable _ inferInstance (Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.1 b.2 a))

theorem Hyp213.eq_bot_of_odd [Finite K] (h : Hyp213 T) {Q : Subgroup K} (hQ : Q.Normal)
    (hodd : Odd (Nat.card Q)) : Q = ⊥ := by
  have hcen := oddCore_le_center h.isWC h.four_le Q
    (by rw [h.normalClosure_eq_top]; exact le_top) (fun k _ n hn => hQ.conj_mem n hn k) hodd
  refine eq_bot_iff.2 fun n hn => ?_
  have : n ∈ Subgroup.center K := Subgroup.mem_center_iff.2 fun g =>
    (hcen n hn g (by rw [h.normalClosure_eq_top]; exact Subgroup.mem_top g)).symm
  rwa [h.center_eq_bot] at this

theorem Hyp213.eq_bot_of_odd_of_le [Finite K] (h : Hyp213 T) {M : Subgroup K} (hM : M.Normal)
    {R : Subgroup K} (hRM : R ≤ M) (hRn : M ≤ Subgroup.normalizer (R : Set K))
    (hodd : Odd (Nat.card R)) : R = ⊥ := by
  let p : Subgroup K → Prop := fun Q =>
    Q ≤ M ∧ M ≤ Subgroup.normalizer (Q : Set K) ∧ Odd (Nat.card Q)
  have hsup : ∀ {Q₁ Q₂ : Subgroup K}, p Q₁ → p Q₂ → p (Q₁ ⊔ Q₂) := by
    rintro Q₁ Q₂ ⟨h1M, h1n, h1o⟩ ⟨h2M, h2n, h2o⟩
    refine ⟨sup_le h1M h2M, fun m hm => mem_normalizer_iff_conjSubgroup_eq.2 ?_,
      odd_card_sup_of_le_normalizer (h2M.trans h1n) h1o h2o⟩
    rw [conjSubgroup_sup, mem_normalizer_iff_conjSubgroup_eq.1 (h1n hm),
      mem_normalizer_iff_conjSubgroup_eq.1 (h2n hm)]
  have hconj : ∀ {Q : Subgroup K}, p Q → ∀ g : K, p (conjSubgroup g Q) := by
    rintro Q ⟨hQM, hQn, hQo⟩ g
    refine ⟨fun x hx => ?_, fun m hm => ?_, by rw [card_conjSubgroup]; exact hQo⟩
    · have := hM.conj_mem _ (hQM (mem_conjSubgroup.1 hx)) g
      simpa [mul_assoc] using this
    · have hgm : g⁻¹ * m * g ∈ M := by simpa using hM.conj_mem m hm g⁻¹
      rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_conjSubgroup,
        show m * g = g * (g⁻¹ * m * g) by group, ← conjSubgroup_conjSubgroup,
        mem_normalizer_iff_conjSubgroup_eq.1 (hQn hgm)]
  obtain ⟨Q₀, hRQ₀, hmax⟩ := Finite.exists_le_maximal (p := p) (a := R) ⟨hRM, hRn, hodd⟩
  have hQ₀ : Q₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have heq := hmax.eq_of_le (hsup hmax.prop (hconj hmax.prop g)) le_sup_left
    have hle : conjSubgroup g Q₀ ≤ Q₀ := calc
      conjSubgroup g Q₀ ≤ Q₀ ⊔ conjSubgroup g Q₀ := le_sup_right
      _ = Q₀ := heq.symm
    exact hle (mem_conjSubgroup.2 (by simpa [mul_assoc] using hn))
  have := h.eq_bot_of_odd hQ₀ hmax.prop.2.2
  exact eq_bot_iff.2 (hRQ₀.trans this.le)

end OddCore

section StepA

variable {K : Type*} [Group K] {T : Subgroup K}

theorem conj_mem_of_forall_commute [Finite K] (hT : IsWC T) {s : K} (hs : s ∈ T) (hs1 : s ≠ 1)
    (g : K) (hx : ∀ t ∈ T, g * s * g⁻¹ * t = t * (g * s * g⁻¹)) : g * s * g⁻¹ ∈ T := by
  have hxT' : g * s * g⁻¹ ∈ conjSubgroup g T :=
    mem_conjSubgroup.2 (by simpa [mul_assoc] using hs)
  have hx1 : g * s * g⁻¹ ≠ 1 := by
    intro h1
    apply hs1
    have : s = g⁻¹ * (g * s * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hT' := hT.conj g
  have hTN : T ≤ Subgroup.normalizer (conjSubgroup g T : Set K) := fun t ht =>
    hT'.centralizer_le_normalizer hxT' hx1 (Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hx t ht)
  have hTeq : T = conjSubgroup g T :=
    eq_of_le_normalizer_of_isWC hT' ⟨g⁻¹, by
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]⟩ hTN
  rw [hTeq]
  exact hxT'

theorem conj_eq_of_commute [Finite K] (hT : IsWC T) {M : Subgroup K} (hM : M.Normal)
    (hMT : M ⊓ T = ⊥) {a : K} (ha : a ∈ T) (ha1 : a ≠ 1) {m : K} (hm : m ∈ M)
    (hc : m * a * m⁻¹ * a = a * (m * a * m⁻¹)) : m * a * m⁻¹ = a := by
  have haa : a * a = 1 := by simpa [pow_two] using hT.1.2 a ha
  set a' := m * a * m⁻¹ with ha'
  have ha'2 : a' * a' = 1 := by
    calc a' * a' = m * (a * a) * m⁻¹ := by simp only [ha']; group
      _ = 1 := by rw [haa]; group
  have hzN : a' ∈ Subgroup.normalizer (T : Set K) :=
    hT.centralizer_le_normalizer ha ha1 (Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hc.symm)
  have hP : IsPGroup 2 ↥(Subgroup.zpowers a' ⊔ T) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_two_zpowers_of_mul_self ha'2)
      (isPGroup_two_of_isElemAbelian hT.1) (Subgroup.zpowers_le.2 hzN)
  set u := a⁻¹ * a' with hu
  have huP : u ∈ Subgroup.zpowers a' ⊔ T :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right (T.inv_mem ha))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers a'))
  have hle : conjSubgroup u T ≤ Subgroup.zpowers a' ⊔ T := by
    intro x hx
    have h1 : u⁻¹ * x * u ∈ T := mem_conjSubgroup.1 hx
    have : u * (u⁻¹ * x * u) * u⁻¹ ∈ Subgroup.zpowers a' ⊔ T :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ huP (Subgroup.mem_sup_right h1))
        ((Subgroup.zpowers a' ⊔ T).inv_mem huP)
    simpa [mul_assoc] using this
  have hu1 : conjSubgroup u T = T := eq_of_conj_le_pGroup hT hP le_sup_right hle
  have hun : u ∈ Subgroup.normalizer (T : Set K) := mem_normalizer_of_conjSubgroup_eq hu1
  have hum : u ∈ M := by
    have h1 : a⁻¹ * m * a⁻¹⁻¹ ∈ M := hM.conj_mem m hm a⁻¹
    have e : u = (a⁻¹ * m * a⁻¹⁻¹) * m⁻¹ := by simp only [hu, ha']; group
    rw [e]
    exact M.mul_mem h1 (M.inv_mem hm)
  have hucomm : ∀ t ∈ T, u * t = t * u := by
    intro t ht
    have h1 : ⁅u, t⁆ ∈ T := comm_mem_of_mem_normalizer hun ht
    have h2 : ⁅u, t⁆ ∈ M := by
      have := M.mul_mem hum (hM.conj_mem u⁻¹ (M.inv_mem hum) t)
      simpa [commutatorElement_def, mul_assoc] using this
    have h3 : ⁅u, t⁆ ∈ M ⊓ T := ⟨h2, h1⟩
    rw [hMT, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  have ha'eq : a' = a * u := by simp [hu]
  have ha'T : a' ∈ T := by
    refine conj_mem_of_forall_commute hT ha ha1 m fun t ht => ?_
    have e : m * a * m⁻¹ = a * u := ha'eq
    rw [e, mul_assoc, hucomm t ht, ← mul_assoc, elemAbelian_mul_comm hT.1 ha ht, mul_assoc]
  have huT : u ∈ T := T.mul_mem (T.inv_mem ha) ha'T
  have hu0 : u ∈ M ⊓ T := ⟨hum, huT⟩
  rw [hMT, Subgroup.mem_bot] at hu0
  rw [ha'eq, hu0, mul_one]

theorem conj_eq_of_mem_sup_of_commute [Finite K] (hT : IsWC T) {M : Subgroup K} (hM : M.Normal)
    (hMT : M ⊓ T = ⊥) {a : K} (ha : a ∈ T) (ha1 : a ≠ 1) {g : K}
    (hg : g ∈ M ⊔ Subgroup.zpowers a) (hc : g * a * g⁻¹ * a = a * (g * a * g⁻¹)) :
    g * a * g⁻¹ = a := by
  have hg' : g ∈ (M : Set K) * (Subgroup.zpowers a : Set K) := by
    rw [← Subgroup.normal_mul]
    exact hg
  obtain ⟨m, hm, c, hc', rfl⟩ := hg'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
  have e : m * a ^ k * a * (m * a ^ k)⁻¹ = m * a * m⁻¹ := by group
  rw [e] at hc ⊢
  exact conj_eq_of_commute hT hM hMT ha ha1 hm hc

end StepA

section ZStarStep

variable {K : Type} [Group K] [Finite K] {T : Subgroup K}

theorem exists_odd_subgroup_commutators {M : Subgroup K} (hM : M.Normal) {a : K} (ha1 : a ≠ 1)
    (haa : a * a = 1)
    (hiso : ∀ g ∈ M ⊔ Subgroup.zpowers a,
      g * a * g⁻¹ * a = a * (g * a * g⁻¹) → g * a * g⁻¹ = a) :
    ∃ R : Subgroup K, R ≤ M ∧ M ≤ Subgroup.normalizer (R : Set K) ∧ Odd (Nat.card R) ∧
      ∀ m ∈ M, m * a * m⁻¹ * a⁻¹ ∈ R := by
  classical
  let H : Subgroup K := M ⊔ Subgroup.zpowers a
  have haH : a ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hMH : M ≤ H := le_sup_left
  have : Fintype H := Fintype.ofFinite H
  obtain ⟨N', hN'n, hN'odd, hN'c⟩ := CFSG.ZStar.glauberman_zStar H ⟨a, haH⟩
    (fun h => ha1 (congrArg Subtype.val h)) (Subtype.ext haa)
    (fun g hg => Subtype.ext (hiso g.1 g.2 (congrArg Subtype.val hg)))
  refine ⟨M ⊓ N'.map H.subtype, inf_le_left, le_normalizer_of_forall_conj fun m hm r hr => ?_,
    ?_, fun m hm => ?_⟩
  · refine ⟨M.mul_mem (M.mul_mem hm hr.1) (M.inv_mem hm), ?_⟩
    obtain ⟨n, hn, hnr⟩ := hr.2
    refine ⟨⟨m, hMH hm⟩ * n * ⟨m, hMH hm⟩⁻¹, hN'n.conj_mem n hn ⟨m, hMH hm⟩, ?_⟩
    simp [← hnr]
  · have h1 : Nat.card ↥(M ⊓ N'.map H.subtype) ∣ Nat.card ↥(N'.map H.subtype) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [Subgroup.card_map_of_injective H.subtype_injective] at h1
    exact Odd.of_dvd_nat hN'odd h1
  · refine ⟨?_, ⟨_, hN'c ⟨m, hMH hm⟩, rfl⟩⟩
    have := M.mul_mem hm (hM.conj_mem m⁻¹ (M.inv_mem hm) a)
    simpa [mul_assoc] using this

theorem Hyp213.eq_bot_of_inf_eq_bot (h : Hyp213 T) {M : Subgroup K} (hM : M.Normal)
    (hMT : M ⊓ T = ⊥) : M = ⊥ := by
  have hcomm : ∀ a ∈ T, ∀ m ∈ M, m * a = a * m := by
    intro a ha m hm
    by_cases ha1 : a = 1
    · subst ha1
      simp
    have haa : a * a = 1 := by simpa [pow_two] using h.isWC.1.2 a ha
    obtain ⟨R, hRM, hRn, hRodd, hRc⟩ := exists_odd_subgroup_commutators hM ha1 haa
      (fun g hg hc => conj_eq_of_mem_sup_of_commute h.isWC hM hMT ha ha1 hg hc)
    have hR : R = ⊥ := h.eq_bot_of_odd_of_le hM hRM hRn hRodd
    have h1 := hRc m hm
    rw [hR, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hMc : ∀ m ∈ M, ∀ k ∈ Subgroup.normalClosure (T : Set K), m * k = k * m := by
    intro m hm
    refine mul_comm_of_mem_normalClosure fun g t ht => ?_
    have hgm : g⁻¹ * m * g ∈ M := by simpa using hM.conj_mem m hm g⁻¹
    have h1 := hcomm t ht _ hgm
    calc m * (g * t * g⁻¹) = g * ((g⁻¹ * m * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * m * g)) * g⁻¹ := by rw [h1]
      _ = g * t * g⁻¹ * m := by group
  refine eq_bot_iff.2 fun m hm => ?_
  have : m ∈ Subgroup.center K := Subgroup.mem_center_iff.2 fun g =>
    (hMc m hm g (by rw [h.normalClosure_eq_top]; exact Subgroup.mem_top g)).symm
  rwa [h.center_eq_bot] at this

theorem Hyp213.inf_ne_bot (h : Hyp213 T) {M : Subgroup K} (hM : M.Normal) (hM1 : M ≠ ⊥) :
    M ⊓ T ≠ ⊥ := fun hMT => hM1 (h.eq_bot_of_inf_eq_bot hM hMT)

end ZStarStep

section StepB

variable {K : Type*} [Group K]

theorem inf_conjSubgroup_ne_bot {T N : Subgroup K} (hN : N.Normal) (hE : T ⊓ N ≠ ⊥) (g : K) :
    conjSubgroup g T ⊓ N ≠ ⊥ := by
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE
  have hy1' : g * y * g⁻¹ ≠ 1 := by
    intro h1
    apply hy1
    refine Subtype.ext ?_
    show y = 1
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  refine (Subgroup.ne_bot_iff_exists_ne_one).2 ⟨⟨g * y * g⁻¹, ⟨?_, hN.conj_mem y hy.2 g⟩⟩, ?_⟩
  · exact mem_conjSubgroup.2 (by simpa [mul_assoc] using hy.1)
  · exact fun h => hy1' (congrArg Subtype.val h)

theorem false_of_swap [Finite K] {T : Subgroup K} (hT : IsWC T) {N : Subgroup K}
    (hE : T ⊓ N ≠ ⊥) {X X' : Subgroup K} (hXN : X ≤ N) (hX'N : X' ≤ N)
    (hXn : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) (hX'n : ∀ n ∈ N, ∀ x ∈ X', n * x * n⁻¹ ∈ X')
    (hXX' : X ⊓ X' = ⊥) [IsSimpleGroup X] (hnc : ∃ x y : X, x * y ≠ y * x) {a : K}
    (haT : a ∈ T) (ha1 : a ≠ 1) (haX : ∀ x ∈ X, a * x * a⁻¹ ∈ X')
    (haX' : ∀ x ∈ X', a * x * a⁻¹ ∈ X) : False := by
  have haa : a * a = 1 := by simpa [pow_two] using hT.1.2 a haT
  have hcomm : ∀ x ∈ X, ∀ y ∈ X', x * y = y * x := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ X' := X'.mul_mem (hX'n x (hXN hx) y hy) (X'.inv_mem hy)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ X := by
      have := X.mul_mem hx (hXn y (hX'N hy) x⁻¹ (X.inv_mem hx))
      simpa [mul_assoc] using this
    have h3 : x * y * x⁻¹ * y⁻¹ ∈ X ⊓ X' := ⟨h2, h1⟩
    rw [hXX', Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  have huniq : ∀ u₁ ∈ X, ∀ u₂ ∈ X, ∀ v₁ ∈ X', ∀ v₂ ∈ X', u₁ * v₁ = u₂ * v₂ →
      u₁ = u₂ ∧ v₁ = v₂ := by
    intro u₁ hu₁ u₂ hu₂ v₁ hv₁ v₂ hv₂ h
    have h1 : u₂⁻¹ * u₁ = v₂ * v₁⁻¹ := by
      calc u₂⁻¹ * u₁ = u₂⁻¹ * (u₁ * v₁) * v₁⁻¹ := by group
        _ = u₂⁻¹ * (u₂ * v₂) * v₁⁻¹ := by rw [h]
        _ = v₂ * v₁⁻¹ := by group
    have h2 : u₂⁻¹ * u₁ ∈ X ⊓ X' :=
      ⟨X.mul_mem (X.inv_mem hu₂) hu₁, h1 ▸ X'.mul_mem hv₂ (X'.inv_mem hv₁)⟩
    rw [hXX', Subgroup.mem_bot] at h2
    have h3 : v₂ * v₁⁻¹ = 1 := h1 ▸ h2
    exact ⟨(inv_mul_eq_one.1 h2).symm, (mul_inv_eq_one.1 h3).symm⟩
  let δ : X →* K := MonoidHom.mk' (fun x => (x : K) * (a * (x : K) * a⁻¹)) (by
    intro x y
    have hc : (y : K) * (a * (x : K) * a⁻¹) = (a * (x : K) * a⁻¹) * (y : K) :=
      hcomm y y.2 _ (haX x x.2)
    change ((x * y : X) : K) * (a * ((x * y : X) : K) * a⁻¹) =
      ((x : K) * (a * (x : K) * a⁻¹)) * ((y : K) * (a * (y : K) * a⁻¹))
    calc ((x * y : X) : K) * (a * ((x * y : X) : K) * a⁻¹)
        = (x : K) * ((y : K) * (a * (x : K) * a⁻¹)) * (a * (y : K) * a⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = (x : K) * ((a * (x : K) * a⁻¹) * (y : K)) * (a * (y : K) * a⁻¹) := by rw [hc]
      _ = ((x : K) * (a * (x : K) * a⁻¹)) * ((y : K) * (a * (y : K) * a⁻¹)) := by group)
  have hδ : ∀ x : X, δ x = (x : K) * (a * (x : K) * a⁻¹) := fun x => rfl
  have hδinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hδ] at hx
    have := huniq (x : K) x.2 1 X.one_mem (a * (x : K) * a⁻¹) (haX x x.2) 1 X'.one_mem
      (by rw [hx, mul_one])
    exact Subtype.ext this.1
  have hδC : ∀ x : X, δ x ∈ Subgroup.centralizer ({a} : Set K) := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hx' : a * (x : K) * a⁻¹ ∈ X' := haX x x.2
    have hcx : (x : K) * (a * (x : K) * a⁻¹) = (a * (x : K) * a⁻¹) * (x : K) :=
      hcomm x x.2 _ hx'
    have e : a * (a * (x : K) * a⁻¹) * a⁻¹ = x := by
      calc a * (a * (x : K) * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
        _ = x := by rw [haa]; group
    show a * ((x : K) * (a * (x : K) * a⁻¹)) = ((x : K) * (a * (x : K) * a⁻¹)) * a
    calc a * ((x : K) * (a * (x : K) * a⁻¹))
        = (a * (x : K) * a⁻¹) * (a * (a * (x : K) * a⁻¹) * a⁻¹) * a := by group
      _ = (a * (x : K) * a⁻¹) * (x : K) * a := by rw [e]
      _ = (x : K) * (a * (x : K) * a⁻¹) * a := by rw [← hcx]
  have hδN : ∀ x : X, δ x ∈ Subgroup.normalizer (T : Set K) := fun x =>
    hT.centralizer_le_normalizer haT ha1 (hδC x)
  have hC : ∀ u ∈ X, ∀ v ∈ X', u * v ∈ T → u * v = 1 := by
    intro u hu v hv huv
    have h1 : a * (u * v) * a⁻¹ = u * v := by
      rw [elemAbelian_mul_comm hT.1 haT huv]
      group
    have h2 : (a * v * a⁻¹) * (a * u * a⁻¹) = u * v := by
      calc (a * v * a⁻¹) * (a * u * a⁻¹) = (a * u * a⁻¹) * (a * v * a⁻¹) :=
            hcomm _ (haX' v hv) _ (haX u hu)
        _ = a * (u * v) * a⁻¹ := by group
        _ = u * v := h1
    obtain ⟨-, e2⟩ := huniq _ (haX' v hv) u hu _ (haX u hu) v hv h2
    have hδu : δ ⟨u, hu⟩ = u * v := by
      rw [hδ]
      show u * (a * u * a⁻¹) = u * v
      rw [e2]
    have hB : (T.comap δ).Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_comap] at hx ⊢
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_of_mem_normalizer (hδN g) hx⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.comap δ) with hb | hb
    · have hmem : (⟨u, hu⟩ : X) ∈ T.comap δ := by
        rw [Subgroup.mem_comap, hδu]
        exact huv
      rw [hb, Subgroup.mem_bot] at hmem
      have hu1 : u = 1 := congrArg Subtype.val hmem
      have hv1 : v = 1 := by rw [← e2, hu1]; group
      rw [hu1, hv1, mul_one]
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have hx : δ x ∈ T := by
        have : x ∈ T.comap δ := by rw [hb]; exact Subgroup.mem_top x
        exact this
      have hy : δ y ∈ T := by
        have : y ∈ T.comap δ := by rw [hb]; exact Subgroup.mem_top y
        exact this
      apply hδinj
      rw [map_mul, map_mul]
      exact elemAbelian_mul_comm hT.1 hx hy
  have hD : ∀ e ∈ T ⊓ N, ∀ x ∈ X, e * x * e⁻¹ = x := by
    intro e he x hx
    have hx' : a * x * a⁻¹ ∈ X' := haX x hx
    have hp : e * x * e⁻¹ ∈ X := hXn e he.2 x hx
    have hp' : e * (a * x * a⁻¹) * e⁻¹ ∈ X' := hX'n e he.2 _ hx'
    have hcT : (x * (a * x * a⁻¹)) * e * (x * (a * x * a⁻¹))⁻¹ * e⁻¹ ∈ T :=
      T.mul_mem (conj_mem_of_mem_normalizer (hδN ⟨x, hx⟩) he.1) (T.inv_mem he.1)
    have hcform : (x * (a * x * a⁻¹)) * e * (x * (a * x * a⁻¹))⁻¹ * e⁻¹ =
        (x * (e * x * e⁻¹)⁻¹) * ((a * x * a⁻¹) * (e * (a * x * a⁻¹) * e⁻¹)⁻¹) := by
      have hAB := hcomm _ (X.inv_mem hp) _ (X'.mul_mem hx' (X'.inv_mem hp'))
      calc (x * (a * x * a⁻¹)) * e * (x * (a * x * a⁻¹))⁻¹ * e⁻¹
          = x * (((a * x * a⁻¹) * (e * (a * x * a⁻¹) * e⁻¹)⁻¹) * (e * x * e⁻¹)⁻¹) := by group
        _ = x * ((e * x * e⁻¹)⁻¹ * ((a * x * a⁻¹) * (e * (a * x * a⁻¹) * e⁻¹)⁻¹)) := by
          rw [hAB]
        _ = (x * (e * x * e⁻¹)⁻¹) * ((a * x * a⁻¹) * (e * (a * x * a⁻¹) * e⁻¹)⁻¹) := by group
    have h1 : (x * (e * x * e⁻¹)⁻¹) * ((a * x * a⁻¹) * (e * (a * x * a⁻¹) * e⁻¹)⁻¹) = 1 :=
      hC _ (X.mul_mem hx (X.inv_mem hp)) _ (X'.mul_mem hx' (X'.inv_mem hp'))
        (by rw [← hcform]; exact hcT)
    have h2 := huniq _ (X.mul_mem hx (X.inv_mem hp)) 1 X.one_mem _
      (X'.mul_mem hx' (X'.inv_mem hp')) 1 X'.one_mem (by rw [h1, mul_one])
    exact (mul_inv_eq_one.1 h2.1).symm
  obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hXN' : ∀ x ∈ X, x ∈ Subgroup.normalizer (T : Set K) := by
    intro x hx
    refine hT.centralizer_le_normalizer hb.1 hb1'
      (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have h1 := hD b hb x hx
    calc b * x = (b * x * b⁻¹) * b := by group
      _ = x * b := by rw [h1]
  have hall : ∀ x ∈ X, x = 1 := by
    intro x hx
    have hxa : x * a * x⁻¹ * a⁻¹ ∈ T :=
      T.mul_mem (conj_mem_of_mem_normalizer (hXN' x hx) haT) (T.inv_mem haT)
    have hv : a * x⁻¹ * a⁻¹ ∈ X' := haX x⁻¹ (X.inv_mem hx)
    have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    have h1 : x * (a * x⁻¹ * a⁻¹) = 1 := hC x hx _ hv (by rw [← e]; exact hxa)
    exact (huniq x hx 1 X.one_mem _ hv 1 X'.one_mem (by rw [h1, mul_one])).1
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  exact hx (Subtype.ext (hall x x.2))

theorem conjSubgroup_normalized {N X : Subgroup K} (hN : N.Normal)
    (hXn : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) (a : K) :
    ∀ n ∈ N, ∀ y ∈ conjSubgroup a X, n * y * n⁻¹ ∈ conjSubgroup a X := by
  intro n hn y hy
  rw [mem_conjSubgroup] at hy ⊢
  have hn' : a⁻¹ * n * a ∈ N := by simpa using hN.conj_mem n hn a⁻¹
  have := hXn _ hn' _ hy
  convert this using 1
  group

theorem eq_or_inf_conj_eq_bot [Finite K] {N : Subgroup K} (hN : N.Normal) {X : Subgroup K}
    (hXN : X ≤ N) (hXn : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) [IsSimpleGroup X] (a : K) :
    conjSubgroup a X = X ∨ X ⊓ conjSubgroup a X = ⊥ := by
  have hX'n := conjSubgroup_normalized hN hXn a
  have hnormal : ((X ⊓ conjSubgroup a X).subgroupOf X).Normal := by
    refine ⟨fun z hz g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact ⟨X.mul_mem (X.mul_mem g.2 hz.1) (X.inv_mem g.2), hX'n g (hXN g.2) _ hz.2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((X ⊓ conjSubgroup a X).subgroupOf X) with
    h | h
  · right
    refine eq_bot_iff.2 fun z hz => ?_
    have hz' : (⟨z, hz.1⟩ : X) ∈ (X ⊓ conjSubgroup a X).subgroupOf X := hz
    rw [h, Subgroup.mem_bot] at hz'
    exact congrArg Subtype.val hz'
  · left
    have hle : X ≤ conjSubgroup a X := fun x hx => by
      have : (⟨x, hx⟩ : X) ∈ (X ⊓ conjSubgroup a X).subgroupOf X := by
        rw [h]
        exact Subgroup.mem_top _
      exact this.2
    exact conjSubgroup_eq_of_ge hle

theorem mem_of_mem_of_mem_T [Finite K] {T : Subgroup K} (hT : IsWC T) {N : Subgroup K}
    (hN : N.Normal) (hE : T ⊓ N ≠ ⊥) {X : Subgroup K} (hXN : X ≤ N)
    (hXn : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) [IsSimpleGroup X]
    (hnc : ∃ x y : X, x * y ≠ y * x) {a : K} (haT : a ∈ T) :
    ∀ x ∈ X, a * x * a⁻¹ ∈ X := by
  intro x hx
  by_cases ha1 : a = 1
  · simpa [ha1] using hx
  have haa : a * a = 1 := by simpa [pow_two] using hT.1.2 a haT
  rcases eq_or_inf_conj_eq_bot hN hXN hXn a with h | h
  · have : a * x * a⁻¹ ∈ conjSubgroup a X := mem_conjSubgroup.2 (by simpa [mul_assoc] using hx)
    rwa [h] at this
  · exfalso
    refine false_of_swap hT hE hXN (fun y hy => ?_) hXn (conjSubgroup_normalized hN hXn a) h hnc
      haT ha1 (fun y hy => mem_conjSubgroup.2 (by simpa [mul_assoc] using hy)) (fun y hy => ?_)
    · have := hN.conj_mem _ (hXN (mem_conjSubgroup.1 hy)) a
      simpa [mul_assoc] using this
    · have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
      have h1 := mem_conjSubgroup.1 hy
      rw [hinv] at h1 ⊢
      exact h1

end StepB

section MinimalNormal

variable {K : Type} [Group K] [Finite K] {T : Subgroup K}

theorem exists_normal_minimal_le_of_ne_bot {M : Subgroup K} (hM : M.Normal) (hM1 : M ≠ ⊥) :
    ∃ N : Subgroup K, N ≤ M ∧ N.Normal ∧ N ≠ ⊥ ∧
      ∀ M' : Subgroup K, M'.Normal → M' ≤ N → M' = ⊥ ∨ M' = N := by
  obtain ⟨N, ⟨⟨hNn, hN1⟩, hNM⟩, hNmin⟩ :=
    (Set.toFinite {N : Subgroup K | (N.Normal ∧ N ≠ ⊥) ∧ N ≤ M}).exists_minimal
      ⟨M, ⟨hM, hM1⟩, le_rfl⟩
  refine ⟨N, hNM, hNn, hN1, fun M' hM' hle => ?_⟩
  by_cases h0 : M' = ⊥
  · exact Or.inl h0
  · exact Or.inr (le_antisymm hle (hNmin ⟨⟨hM', h0⟩, hle.trans hNM⟩ hle))

theorem Hyp213.isSimpleGroup_of_minimal (h : Hyp213 T) {N : Subgroup K} (hN : N.Normal)
    (hN1 : N ≠ ⊥) (hmin : ∀ M : Subgroup K, M.Normal → M ≤ N → M = ⊥ ∨ M = N) :
    IsSimpleGroup N := by
  have hE : T ⊓ N ≠ ⊥ := by
    rw [inf_comm]
    exact h.inf_ne_bot hN hN1
  obtain ⟨r, S, hr, hSN, hSsimple, -, hSnormal, e, -⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hN hN1 hmin
  have hex : ∃ i : Fin r, ∃ x y : S i, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hNcomm : ∀ n m : N, n * m = m * n := by
      intro n m
      obtain ⟨x, rfl⟩ := e.surjective n
      obtain ⟨y, rfl⟩ := e.surjective m
      rw [← map_mul, ← map_mul]
      congr 1
      funext i
      exact hcon i (x i) (y i)
    exact hN1 (h.eq_bot_of_solvable N hN (Group.isSolvable_of_comm hNcomm))
  obtain ⟨i0, hnc⟩ := hex
  have hXs : IsSimpleGroup (S i0) := hSsimple i0
  have hXn : ∀ n ∈ N, ∀ x ∈ S i0, n * x * n⁻¹ ∈ S i0 := fun n hn x hx =>
    Subgroup.mem_subgroupOf.1
      ((hSnormal i0).conj_mem ⟨x, hSN i0 hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨n, hn⟩)
  have hle : Subgroup.normalClosure (T : Set K) ≤ Subgroup.normalizer (S i0 : Set K) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    obtain ⟨t, ht, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨g, rfl⟩ := isConj_iff.1 hconj
    have hc : g * t * g⁻¹ ∈ conjSubgroup g T :=
      mem_conjSubgroup.2 (by simpa [mul_assoc] using ht)
    have hnT : ∀ a ∈ conjSubgroup g T, ∀ x ∈ S i0, a * x * a⁻¹ ∈ S i0 := fun a ha x hx =>
      mem_of_mem_of_mem_T (h.isWC.conj g) hN (inf_conjSubgroup_ne_bot hN hE g) (hSN i0) hXn hnc
        ha x hx
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hnT _ hc x hx, fun hx => ?_⟩
    have := hnT _ ((conjSubgroup g T).inv_mem hc) _ hx
    simpa [mul_assoc] using this
  have hXnormal : (S i0).Normal := by
    refine Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 ?_)
    rw [← h.normalClosure_eq_top]
    exact hle
  rcases hmin (S i0) hXnormal (hSN i0) with hbot | heq
  · exact absurd hbot ((Subgroup.nontrivial_iff_ne_bot _).1 inferInstance)
  · rw [← heq]
    exact hSsimple i0

theorem Hyp213.eq_of_minimal_normal (h : Hyp213 T) {N M : Subgroup K} (hN : N.Normal)
    (hN1 : N ≠ ⊥) (hminN : ∀ M' : Subgroup K, M'.Normal → M' ≤ N → M' = ⊥ ∨ M' = N)
    (hM : M.Normal) (hM1 : M ≠ ⊥)
    (hminM : ∀ M' : Subgroup K, M'.Normal → M' ≤ M → M' = ⊥ ∨ M' = M) : M = N := by
  by_contra hne
  have hNM : N ⊓ M = ⊥ :=
    CFSG.LocalCores.inf_eq_bot_of_minimal_normal ⟨hN, hN1, hminN⟩ ⟨hM, hM1, hminM⟩ (Ne.symm hne)
  have hMT : M ⊓ T ≠ ⊥ := h.inf_ne_bot hM hM1
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hMT
  have hy1' : y ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
  have hNnorm : ∀ n ∈ N, n ∈ Subgroup.normalizer (T : Set K) := fun n hn =>
    h.isWC.centralizer_le_normalizer hy.2 hy1' (Subgroup.mem_centralizer_iff.2 fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (@CFSG.LocalCores.commute_of_normal_of_inf_eq_bot K _ N M hN hM hNM n y hn
        hy.1).eq.symm)
  have hsimple : IsSimpleGroup N := h.isSimpleGroup_of_minimal hN hN1 hminN
  have hnormal : ((N ⊓ T).subgroupOf N).Normal := by
    refine ⟨fun u hu n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    exact ⟨N.mul_mem (N.mul_mem n.2 hu.1) (N.inv_mem n.2),
      conj_mem_of_mem_normalizer (hNnorm n n.2) hu.2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ T).subgroupOf N) with hb | hb
  · refine h.inf_ne_bot hN hN1 (eq_bot_iff.2 fun z hz => ?_)
    have hz' : (⟨z, hz.1⟩ : N) ∈ (N ⊓ T).subgroupOf N := hz
    rw [hb, Subgroup.mem_bot] at hz'
    exact congrArg Subtype.val hz'
  · have hNT : ∀ n ∈ N, n ∈ T := fun n hn => by
      have : (⟨n, hn⟩ : N) ∈ (N ⊓ T).subgroupOf N := by
        rw [hb]
        exact Subgroup.mem_top _
      exact this.2
    have hcomm : ∀ n m : N, n * m = m * n := fun n m =>
      Subtype.ext (elemAbelian_mul_comm h.isWC.1 (hNT n n.2) (hNT m m.2))
    exact hN1 (h.eq_bot_of_solvable N hN (Group.isSolvable_of_comm hcomm))

end MinimalNormal

theorem lemma213 : Lemma213Stmt := by
  unfold Lemma213Stmt
  intro K _ _ T hT h4 hK hS
  have h : Hyp213 T := ⟨hT, h4, hK, hS⟩
  have htop : (⊤ : Subgroup K) ≠ ⊥ := by
    intro htb
    have hTb : T = ⊥ := eq_bot_iff.2 (htb ▸ le_top)
    rw [hTb, Subgroup.card_bot] at h4
    omega
  obtain ⟨N, -, hN, hN1, hmin⟩ := exists_normal_minimal_le_of_ne_bot (M := ⊤) inferInstance htop
  refine ⟨N, hN, hN1, h.isSimpleGroup_of_minimal hN hN1 hmin, h.inf_ne_bot hN hN1, ?_⟩
  intro M hM hM1
  obtain ⟨N₀, hN₀M, hN₀n, hN₀1, hN₀min⟩ := exists_normal_minimal_le_of_ne_bot hM hM1
  have := h.eq_of_minimal_normal hN hN1 hmin hN₀n hN₀1 hN₀min
  rw [← this]
  exact hN₀M

end CFSG.CGT.Timmesfeld75
