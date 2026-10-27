module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Def
public import CFSG.RankThree.PartOne.SolD3.Block
public import CFSG.CGT.PushingUpLit.LIT.A4.Setup

public section

namespace CFSG.CGT.PushingUpLit.A4

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open scoped commutatorElement

section ConjSub

variable {G : Type} [Group G]

theorem conjSub_injective (g : G) : Function.Injective (conjSub g) := fun H K h => by
  have := congrArg (conjSub g⁻¹) h
  rwa [conjSub_conjSub, conjSub_conjSub, inv_mul_cancel, conjSub_one, conjSub_one] at this

theorem conjSub_inf (g : G) (H K : Subgroup G) :
    conjSub g (H ⊓ K) = conjSub g H ⊓ conjSub g K := by
  ext x
  simp only [mem_conjSub_iff, Subgroup.mem_inf]

theorem conjSub_card (g : G) (H : Subgroup G) : Nat.card ↥(conjSub g H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

end ConjSub

section Commuting

variable {G : Type} [Group G]

theorem commute_of_mem_sup {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, Commute h k)
    (hH : ∀ h ∈ H, ∀ h' ∈ H, Commute h h') (hK : ∀ k ∈ K, ∀ k' ∈ K, Commute k k') :
    ∀ x ∈ H ⊔ K, ∀ y ∈ H ⊔ K, Commute x y := by
  have hsup : H ⊔ K = Subgroup.closure ((H : Set G) ∪ K) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hsup]
  intro x hx y hy
  have h1 : ∀ g ∈ (H : Set G) ∪ K, ∀ y ∈ Subgroup.closure ((H : Set G) ∪ K), Commute g y := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hg with hg | hg <;> rcases hy with hy | hy
      · exact hH g hg y hy
      · exact hHK g hg y hy
      · exact (hHK y hy g hg).symm
      · exact hK g hg y hy
    | one => exact Commute.one_right g
    | mul y y' _ _ hy hy' => exact hy.mul_right hy'
    | inv y _ hy => exact hy.inv_right
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h1 x hx y hy
  | one => exact Commute.one_left y
  | mul x x' _ _ hx hx' => exact hx.mul_left hx'
  | inv x _ hx => exact hx.inv_left

theorem sq_eq_one_of_mem_sup {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, Commute h k)
    (hH : ∀ h ∈ H, h * h = 1) (hK : ∀ k ∈ K, k * k = 1)
    (hHc : ∀ h ∈ H, ∀ h' ∈ H, Commute h h') (hKc : ∀ k ∈ K, ∀ k' ∈ K, Commute k k') :
    ∀ x ∈ H ⊔ K, x * x = 1 := by
  have hcomm := commute_of_mem_sup hHK hHc hKc
  have hsup : H ⊔ K = Subgroup.closure ((H : Set G) ∪ K) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have key : ∀ x ∈ Subgroup.closure ((H : Set G) ∪ K), x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hH x hx
      · exact hK x hx
    | one => simp
    | mul x y hxm hym hx2 hy2 =>
      have hxy : Commute x y := hcomm x (hsup ▸ hxm) y (hsup ▸ hym)
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy.eq]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx2, hy2, mul_one]
    | inv x hxm hx2 =>
      have : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      rw [this, hx2, inv_one]
  rw [hsup]
  exact key

end Commuting

section ConjCore

variable {G : Type} [Group G]

theorem conjSub_sup (g : G) (H K : Subgroup G) : conjSub g (H ⊔ K) = conjSub g H ⊔ conjSub g K :=
  Subgroup.map_sup H K _

theorem conjSub_centralizer (g : G) (H : Subgroup G) :
    conjSub g (Subgroup.centralizer (H : Set G)) = Subgroup.centralizer (conjSub g H : Set G) := by
  ext z
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hz y hy
    rw [SetLike.mem_coe, mem_conjSub_iff] at hy
    have h1 := hz (g⁻¹ * y * g) hy
    calc y * z = g * (g⁻¹ * y * g * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = z * y := by group
  · intro hz y hy
    have h1 := hz (g * y * g⁻¹) (conj_mem_conjSub hy)
    calc y * (g⁻¹ * z * g) = g⁻¹ * ((g * y * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * y * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * z * g * y := by group

theorem conjSub_map_le (g : G) {H K : Subgroup G} (h : H ≤ K) : conjSub g H ≤ conjSub g K :=
  Subgroup.map_mono h

theorem pCoreOf_conj_le (g : G) (X : Subgroup G) :
    conjSub g (pCoreOf 2 X) ≤ pCoreOf 2 (conjSub g X) := by
  refine SolK.le_pCoreOf_of_normalized (conjSub_map_le g (SolK.pCoreOf_le_self X)) ?_ ?_
  · intro h hh x hx
    rw [mem_conjSub_iff] at hh hx ⊢
    have := SolK.pCoreOf_normalized X hh hx
    have e : g⁻¹ * (h * x * h⁻¹) * g = (g⁻¹ * h * g) * (g⁻¹ * x * g) * (g⁻¹ * h * g)⁻¹ := by
      group
    rw [e]
    exact this
  · have : IsPGroup 2 ↥((pCoreOf 2 X).map (MulAut.conj g).toMonoidHom) :=
      (SolK.isPGroup_pCoreOf' X).map _
    exact this

theorem pCoreOf_conj_eq (g : G) (X : Subgroup G) :
    pCoreOf 2 (conjSub g X) = conjSub g (pCoreOf 2 X) := by
  apply le_antisymm
  · have h := pCoreOf_conj_le g⁻¹ (conjSub g X)
    rw [conjSub_conjSub, inv_mul_cancel, conjSub_one] at h
    have h2 := conjSub_map_le g h
    rwa [conjSub_inv_self] at h2
  · exact pCoreOf_conj_le g X

theorem blk3_of_conj {X : Subgroup G} {a : G} (h : SolD3.Blk3 X a) (g : G) :
    SolD3.Blk3 (conjSub g X) (g * a * g⁻¹) where
  mem := conj_mem_conjSub h.mem
  cube := by rw [conj_pow, h.cube]; group
  dec := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    obtain ⟨y, hy, j, hxy⟩ := h.dec _ hx
    refine ⟨g * y * g⁻¹, ?_, j, ?_⟩
    · rw [pCoreOf_conj_eq]
      exact conj_mem_conjSub hy
    · rw [conj_pow]
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * (y * a ^ j) * g⁻¹ := by rw [hxy]
        _ = g * y * g⁻¹ * (g * a ^ j * g⁻¹) := by group
  comm := by
    intro y hy y' hy'
    rw [pCoreOf_conj_eq, mem_conjSub_iff] at hy hy'
    have h1 := h.comm _ hy _ hy'
    calc y * y' = g * (g⁻¹ * y * g * (g⁻¹ * y' * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y' * g * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = y' * y := by group
  sq := by
    intro y hy
    rw [pCoreOf_conj_eq, mem_conjSub_iff] at hy
    have h1 := h.sq _ hy
    calc y * y = g * (g⁻¹ * y * g * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  card := by
    rw [pCoreOf_conj_eq]
    exact (conjSub_card g _).trans h.card
  fix := by
    intro y hy hfix
    rw [pCoreOf_conj_eq, mem_conjSub_iff] at hy
    have h1 := h.fix (g⁻¹ * y * g) hy (by
      have e : a * (g⁻¹ * y * g) * a⁻¹ = g⁻¹ * ((g * a * g⁻¹) * y * (g * a * g⁻¹)⁻¹) * g := by
        group
      rw [e, hfix])
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group

theorem isPGroup_two_of_sq {H : Subgroup G} (h : ∀ x ∈ H, x * x = 1) : IsPGroup 2 H := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  have := h x x.2
  simpa [pow_two] using this

end ConjCore

namespace A4Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (c : A4Cfg G M X)
include c

theorem center_eq_one {z : G} (hz : z ∈ X) (hc : ∀ x ∈ X, z * x = x * z) : z = 1 := by
  obtain ⟨a, haX, ha3, hdec, hVcomm, hVsq, hVcard, hfix⟩ := c.exists_order_three
  obtain ⟨y, hy, j, rfl⟩ := hdec z hz
  have hba : Commute (a ^ j) a := (Commute.refl a).pow_left j
  have hya : a * y * a⁻¹ = y := by
    have h1 : y * a ^ j * a = a * (y * a ^ j) := hc a haX
    have h2 : (y * a) * a ^ j = (a * y) * a ^ j := by
      calc (y * a) * a ^ j = y * (a * a ^ j) := by rw [mul_assoc]
        _ = y * (a ^ j * a) := by rw [hba.eq.symm]
        _ = y * a ^ j * a := by rw [mul_assoc]
        _ = a * (y * a ^ j) := h1
        _ = (a * y) * a ^ j := by rw [mul_assoc]
    have h3 : y * a = a * y := mul_right_cancel h2
    calc a * y * a⁻¹ = y * a * a⁻¹ := by rw [h3]
      _ = y := by group
  have hy1 : y = 1 := hfix y hy hya
  subst hy1
  rw [one_mul] at hc ⊢
  obtain ⟨y', hy', hy'1⟩ : ∃ y' ∈ pCoreOf 2 X, y' ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : pCoreOf 2 X = ⊥ := eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (hcon y hy)
    rw [this, Subgroup.card_bot] at hVcard
    omega
  have hy'X : y' ∈ X := SolK.pCoreOf_le_self X hy'
  have hmod : a ^ j = a ^ (j % 3) := pow_eq_pow_mod j ha3
  have hcy := hc y' hy'X
  rw [hmod] at hcy ⊢
  have hlt : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hj : j % 3
  · simp
  · exfalso
    apply hy'1
    apply hfix y' hy'
    rw [pow_one] at hcy
    calc a * y' * a⁻¹ = y' * a * a⁻¹ := by rw [hcy]
      _ = y' := by group
  · exfalso
    apply hy'1
    apply hfix y' hy'
    have h2 : a ^ 2 * y' * (a ^ 2)⁻¹ = y' := by
      calc a ^ 2 * y' * (a ^ 2)⁻¹ = y' * a ^ 2 * (a ^ 2)⁻¹ := by rw [hcy]
        _ = y' := by group
    have h3 : a * y' * a⁻¹ = a ^ 3 * y' * (a ^ 3)⁻¹ := by
      calc a * y' * a⁻¹ = a * (a ^ 2 * y' * (a ^ 2)⁻¹) * a⁻¹ := by rw [h2]
        _ = a ^ 3 * y' * (a ^ 3)⁻¹ := by group
    rw [h3, ha3]
    group

end A4Cfg

section TwoConjLemmas

variable {G : Type} [Group G] {M X : Subgroup G} {m : G}

theorem twoConj_perm (h : TwoConj M X m) {k : G} (hk : k ∈ M) :
    (conjSub k X = X ∧ conjSub k (conjSub m X) = conjSub m X) ∨
      (conjSub k X = conjSub m X ∧ conjSub k (conjSub m X) = X) := by
  obtain ⟨hm, hne, honly⟩ := h
  have hkm : conjSub k (conjSub m X) = conjSub (k * m) X := conjSub_conjSub k m X
  have h2 := honly (k * m) (M.mul_mem hk hm)
  rcases honly k hk with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exfalso
      apply hne
      have : conjSub k (conjSub m X) = conjSub k X := by rw [hkm, h2, h1]
      exact conjSub_injective k this
    · rw [hkm]
      exact h2
  · right
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · rw [hkm]
      exact h2
    · exfalso
      apply hne
      have : conjSub k (conjSub m X) = conjSub k X := by rw [hkm, h2, h1]
      exact conjSub_injective k this

theorem twoConj_commute [Finite G] (c : A4Cfg G M X) (h : TwoConj M X m) :
    ∀ x ∈ X, ∀ y ∈ conjSub m X, x * y = y * x := by
  intro x hx y hy
  have hcomm := c.commutator_conj_eq_bot h.1 h.2.1
  have hmem : ⁅x, y⁆ ∈ ⁅X, conjSub m X⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hcomm, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.1 hmem

theorem twoConj_inf_eq_bot [Finite G] (c : A4Cfg G M X) (h : TwoConj M X m) :
    X ⊓ conjSub m X = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨hzX, hzY⟩ := Subgroup.mem_inf.1 hz
  exact c.center_eq_one hzX (fun x hx => (twoConj_commute c h x hx z hzY).symm)

end TwoConjLemmas

section BaseTwo

variable {G : Type} [Group G] {M X : Subgroup G} {m : G}

theorem conjSub_baseTwo (h : TwoConj M X m) {k : G} (hk : k ∈ M) :
    conjSub k (baseTwo X m) = baseTwo X m := by
  unfold baseTwo
  rw [conjSub_sup]
  simp only [← pCoreOf_conj_eq]
  rcases twoConj_perm h hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]

theorem baseTwo_comm [Finite G] (c : A4Cfg G M X) (h : TwoConj M X m) :
    ∀ x ∈ baseTwo X m, ∀ y ∈ baseTwo X m, x * y = y * x := by
  obtain ⟨a, ha⟩ := SolD3.exists_blk3 c.short c.nat
  have hb2 := blk3_of_conj ha m
  exact commute_of_mem_sup
    (fun v hv w hw => twoConj_commute c h v (SolK.pCoreOf_le_self X hv) w
      (SolK.pCoreOf_le_self _ hw))
    (fun v hv w hw => ha.comm v hv w hw) (fun v hv w hw => hb2.comm v hv w hw)

theorem baseTwo_sq [Finite G] (c : A4Cfg G M X) (h : TwoConj M X m) :
    ∀ x ∈ baseTwo X m, x * x = 1 := by
  obtain ⟨a, ha⟩ := SolD3.exists_blk3 c.short c.nat
  have hb2 := blk3_of_conj ha m
  exact sq_eq_one_of_mem_sup
    (fun v hv w hw => twoConj_commute c h v (SolK.pCoreOf_le_self X hv) w
      (SolK.pCoreOf_le_self _ hw))
    (fun v hv => ha.sq v hv) (fun v hv => hb2.sq v hv)
    (fun v hv w hw => ha.comm v hv w hw) (fun v hv w hw => hb2.comm v hv w hw)

theorem pCoreOf_le_baseTwo (X : Subgroup G) (m : G) : pCoreOf 2 X ≤ baseTwo X m := le_sup_left

end BaseTwo

end CFSG.CGT.PushingUpLit.A4
