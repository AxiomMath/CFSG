module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Defs
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltPerm
import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Equiv Equiv.Perm

section Perm

variable {α : Type*} {p : ℕ}

theorem tha_dvd_of_pow_apply_eq (hp : p.Prime) {x : Perm α} (hx : x ^ p = 1) {z : α}
    (hz : x z ≠ z) {j : ℕ} (hj : (x ^ j) z = z) : p ∣ j := by
  by_contra hpj
  have hcop : Nat.Coprime j p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpj)
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  apply hz
  have h1 : x = x ^ (j * s) := by
    rw [pow_eq_pow_mod (j * s) hx, hs, pow_one]
  rw [h1, pow_mul]
  exact Perm.pow_apply_eq_self_of_apply_eq_self hj s

theorem tha_pow_apply_mem {x : Perm α} {O : Finset α} (hxO : ∀ w ∈ O, x w ∈ O) (k : ℕ)
    {w : α} (hw : w ∈ O) : (x ^ k) w ∈ O := by
  induction k with
  | zero => simpa using hw
  | succ k ih => rw [pow_succ', Perm.mul_apply]; exact hxO _ ih

theorem tha_exists_pow_apply_eq [DecidableEq α] (hp : p.Prime) {x : Perm α} (hx : x ^ p = 1)
    {O : Finset α} (hO : O.card = p) (hxO : ∀ w ∈ O, x w ∈ O) {z : α} (hzO : z ∈ O)
    (hz : x z ≠ z) {w : α} (hw : w ∈ O) : ∃ k : ℕ, (x ^ k) z = w := by
  have hsub : (Finset.range p).image (fun k => (x ^ k) z) ⊆ O := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
    exact tha_pow_apply_mem hxO k hzO
  have hinj : Set.InjOn (fun k => (x ^ k) z) (Finset.range p : Set ℕ) := by
    have key : ∀ i j : ℕ, i ≤ j → j < p → (x ^ i) z = (x ^ j) z → i = j := by
      intro i j hij hjp h
      have h1 : (x ^ i) ((x ^ (j - i)) z) = (x ^ i) z := by
        rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hij, h]
      have h2 := tha_dvd_of_pow_apply_eq hp hx hz ((x ^ i).injective h1)
      have h3 : j - i = 0 := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
      omega
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases le_total i j with hij | hij
    · exact key i j hij hj h
    · exact (key j i hij hi h.symm).symm
  have hcard : ((Finset.range p).image (fun k => (x ^ k) z)).card = p := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hO])
  rw [← heq] at hw
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hw
  exact ⟨k, hk⟩

theorem tha_apply_ne [DecidableEq α] (hp : p.Prime) {x : Perm α} (hx : x ^ p = 1)
    {O : Finset α} (hO : O.card = p) (hxO : ∀ w ∈ O, x w ∈ O) {z : α} (hzO : z ∈ O)
    (hz : x z ≠ z) {w : α} (hw : w ∈ O) : x w ≠ w := by
  obtain ⟨k, rfl⟩ := tha_exists_pow_apply_eq hp hx hO hxO hzO hz hw
  intro h
  apply hz
  apply (x ^ k).injective
  rw [← Perm.mul_apply, ← pow_succ, pow_succ', Perm.mul_apply, h]

theorem tha_fix [DecidableEq α] (hp : p.Prime) {x : Perm α} (hx : x ^ p = 1) {O : Finset α}
    (hO : O.card = p) (hxO : ∀ w ∈ O, x w ∈ O) {z : α} (hzO : z ∈ O) (hz : x z ≠ z)
    {σ : Perm α} (hσx : Commute σ x) {N : ℕ} (hN : σ ^ N = 1) (hNp : N.Coprime p)
    (hσz : σ z ∈ O) : ∀ w ∈ O, σ w = w := by
  obtain ⟨k, hk⟩ := tha_exists_pow_apply_eq hp hx hO hxO hzO hz hσz
  have hagree : ∀ w ∈ O, σ w = (x ^ k) w := by
    intro w hw
    obtain ⟨l, rfl⟩ := tha_exists_pow_apply_eq hp hx hO hxO hzO hz hw
    rw [← Perm.mul_apply, (hσx.pow_right l).eq, Perm.mul_apply, ← hk, ← Perm.mul_apply,
      ← Perm.mul_apply, ← pow_add, ← pow_add, add_comm]
  have hpow : ∀ m : ℕ, ∀ w ∈ O, (σ ^ m) w = (x ^ (k * m)) w := by
    intro m
    induction m with
    | zero => intro w _; simp
    | succ m ih =>
      intro w hw
      rw [pow_succ, Perm.mul_apply, hagree w hw, ih _ (tha_pow_apply_mem hxO k hw),
        ← Perm.mul_apply, ← pow_add, Nat.mul_succ]
  have hz' : (x ^ (k * N)) z = z := by rw [← hpow N z hzO, hN, Perm.one_apply]
  have hpk : p ∣ k :=
    Nat.Coprime.dvd_of_dvd_mul_right hNp.symm (tha_dvd_of_pow_apply_eq hp hx hz hz')
  have hxk : x ^ k = 1 := by
    obtain ⟨c, rfl⟩ := hpk
    rw [pow_mul, hx, one_pow]
  intro w hw
  rw [hagree w hw, hxk, Perm.one_apply]

theorem tha_mem_iff_of_commute {a σ : Perm α} {O : Finset α} (ha : ∀ z, a z ≠ z ↔ z ∈ O)
    (h : Commute σ a) (z : α) : σ z ∈ O ↔ z ∈ O := by
  rw [← ha, ← ha, ← Perm.mul_apply, ← h.eq, Perm.mul_apply, σ.injective.ne_iff]

theorem tha_commute_of_fix {a σ : Perm α} {O : Finset α} (ha : ∀ z, a z ≠ z ↔ z ∈ O)
    (hσ : ∀ w ∈ O, σ w = w) : Commute σ a :=
  Perm.Disjoint.commute fun w => by
    by_cases hw : w ∈ O
    · exact Or.inl (hσ w hw)
    · exact Or.inr (not_not.mp (mt (ha w).mp hw))

theorem tha_fix_of_commute [DecidableEq α] (hp : p.Prime) {a σ : Perm α} {O : Finset α}
    (hO : O.card = p) (ha : ∀ z, a z ≠ z ↔ z ∈ O) (hap : a ^ p = 1) (h : Commute σ a)
    {N : ℕ} (hN : σ ^ N = 1) (hNp : N.Coprime p) : ∀ w ∈ O, σ w = w := by
  obtain ⟨z, hz⟩ : O.Nonempty := Finset.card_pos.mp (hO ▸ hp.pos)
  exact tha_fix hp hap hO (fun w hw => (tha_mem_iff_of_commute ha (Commute.refl a) w).mpr hw)
    hz ((ha z).mpr hz) h hN hNp ((tha_mem_iff_of_commute ha h z).mpr hz)

theorem tha_eq_one_of_commute [DecidableEq α] (hp : p.Prime) (hp2 : p ≠ 2) {a : Perm α}
    {O : Finset α} (hO : O.card = p) (ha : ∀ z, a z ≠ z ↔ z ∈ O) {U : Subgroup (Perm α)}
    (hU : ∀ σ ∈ U, ∃ e : ℕ, σ ^ 2 ^ e = 1) (haU : ∀ σ ∈ U, a * σ * a⁻¹ ∈ U)
    (hG : ∀ τ ∈ U, Commute τ a → τ = 1) {x : Perm α} (hx : x ^ p = 1) (hxa : Commute x a)
    {z : α} (hz : z ∈ O) (hxz : x z ≠ z) {σ : Perm α} (hσ : σ ∈ U) (hσx : Commute σ x) :
    σ = 1 := by
  have hxO : ∀ w ∈ O, x w ∈ O := fun w hw => (tha_mem_iff_of_commute ha hxa w).mpr hw
  have hcop : ∀ e : ℕ, (2 ^ e).Coprime p := fun e =>
    Nat.Coprime.pow_left e ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have key : ∀ τ ∈ U, Commute τ x → ∀ w ∈ O, τ w ∈ O → τ = 1 := by
    intro τ hτ hτx w hw hτw
    obtain ⟨e, he⟩ := hU τ hτ
    exact hG τ hτ (tha_commute_of_fix ha (tha_fix hp hx hO hxO hw
      (tha_apply_ne hp hx hO hxO hz hxz hw) hτx he (hcop e) hτw))
  by_cases hσz : σ z ∈ O
  · exact key σ hσ hσx z hz hσz
  · have hτU : σ⁻¹ * (a * σ * a⁻¹) ∈ U := U.mul_mem (U.inv_mem hσ) (haU σ hσ)
    have hτx : Commute (σ⁻¹ * (a * σ * a⁻¹)) x :=
      hσx.inv_left.mul_left ((hxa.symm.mul_left hσx).mul_left hxa.symm.inv_left)
    have haz : a z ∈ O := (tha_mem_iff_of_commute ha (Commute.refl a) z).mpr hz
    have hfix : a (σ z) = σ z := not_not.mp (mt (ha (σ z)).mp hσz)
    have hτaz : (σ⁻¹ * (a * σ * a⁻¹)) (a z) = z := by
      simp [Perm.mul_apply, hfix]
    have hτ1 := key _ hτU hτx (a z) haz (by rw [hτaz]; exact hz)
    have h1 : σ = a * σ * a⁻¹ := inv_mul_eq_one.mp hτ1
    refine hG σ hσ ?_
    rw [Commute, SemiconjBy]
    calc σ * a = a * σ * a⁻¹ * a := by rw [← h1]
      _ = a * σ := by group

theorem tha_eq_one_of_fix {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : n < 3 * p)
    {E : Subgroup (Perm (Fin n))} (hcard : Nat.card E = p ^ 2) {a₁ a₂ : Perm (Fin n)}
    {O₁ O₂ : Finset (Fin n)} (h₁ : O₁.card = p) (h₂ : O₂.card = p) (hO : Disjoint O₁ O₂)
    (ha₁ : ∀ z, a₁ z ≠ z ↔ z ∈ O₁) (ha₂ : ∀ z, a₂ z ≠ z ↔ z ∈ O₂)
    (hE₁ : ∀ g ∈ E, Commute g a₁) (hE₂ : ∀ g ∈ E, Commute g a₂) {x : Perm (Fin n)}
    (hx : x ∈ E) (hx₁ : ∀ z ∈ O₁, x z = z) (hx₂ : ∀ z ∈ O₂, x z = z) : x = 1 := by
  by_contra hx1
  obtain ⟨z, hz⟩ : ∃ z, x z ≠ z := by
    by_contra h
    push Not at h
    exact hx1 (Equiv.ext h)
  have hz₁ : z ∉ O₁ := fun h => hz (hx₁ z h)
  have hz₂ : z ∉ O₂ := fun h => hz (hx₂ z h)
  have hdisj : ∀ {a : Perm (Fin n)} {O : Finset (Fin n)}, (∀ z, a z ≠ z ↔ z ∈ O) →
      (∀ g ∈ E, Commute g a) → z ∉ O → Disjoint (MulAction.orbit E z) (O : Set (Fin n)) := by
    intro a O ha hE hzO
    rw [Set.disjoint_left]
    rintro _ ⟨g, rfl⟩ hg
    exact hzO ((tha_mem_iff_of_commute ha (hE g g.2) z).mp hg)
  have horb : (MulAction.orbit E z).ncard = p := by
    rcases AGLEmbeddingD2.AltOrbit.ncard_orbit_eq_one_or hp hp2 hn hcard z with h | h
    · exfalso
      obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp h
      have h1 : z ∈ MulAction.orbit E z := MulAction.mem_orbit_self z
      have h2 : x z ∈ MulAction.orbit E z := ⟨⟨x, hx⟩, rfl⟩
      rw [hy] at h1 h2
      exact hz (h2.trans h1.symm)
    · exact h
  have hcount : (MulAction.orbit E z ∪ ((O₁ : Set (Fin n)) ∪ O₂)).ncard = 3 * p := by
    rw [Set.ncard_union_eq (Set.disjoint_union_right.mpr ⟨hdisj ha₁ hE₁ hz₁, hdisj ha₂ hE₂ hz₂⟩),
      Set.ncard_union_eq (Finset.disjoint_coe.mpr hO), Set.ncard_coe_finset,
      Set.ncard_coe_finset, horb, h₁, h₂]
    ring
  have hle : (MulAction.orbit E z ∪ ((O₁ : Set (Fin n)) ∪ O₂)).ncard ≤ n := by
    calc _ ≤ (Set.univ : Set (Fin n)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = n := by simp [Set.ncard_univ]
  omega

end Perm

section AltOff

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev tha_altOff (s : Finset α) : Subgroup (Perm α) :=
  (alternatingGroup {x : α // x ∉ s}).map (Perm.ofSubtype : Perm {x : α // x ∉ s} →* Perm α)

theorem tha_mem_altOff {s : Finset α} {x : Perm α} (hx : ∀ a ∈ s, x a = a)
    (hsign : Perm.sign x = 1) : x ∈ tha_altOff s := by
  have h₁ : ∀ y, x y ∉ s ↔ y ∉ s := by
    intro y
    constructor
    · intro h hy
      exact h (by rw [hx y hy]; exact hy)
    · intro h hxy
      apply h
      have h3 : x y = y := x.injective (hx _ hxy)
      rw [← h3]
      exact hxy
  have h₂ : ∀ y, x y ≠ y → y ∉ s := fun y hy hys => hy (hx y hys)
  refine ⟨x.subtypePerm h₁, ?_, Perm.ofSubtype_subtypePerm h₁ h₂⟩
  rw [SetLike.mem_coe, Perm.mem_alternatingGroup, Perm.sign_subtypePerm x h₁ h₂, hsign]

theorem tha_apply_eq_of_mem_altOff {s : Finset α} {x : Perm α} (hx : x ∈ tha_altOff s) {a : α}
    (ha : a ∈ s) : x a = a := by
  obtain ⟨y, -, rfl⟩ := hx
  exact Perm.ofSubtype_apply_of_not_mem y (by simpa using ha)

theorem tha_sign_of_mem_altOff {s : Finset α} {x : Perm α} (hx : x ∈ tha_altOff s) :
    Perm.sign x = 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Perm.sign_ofSubtype]
  exact hy

theorem tha_card_compl (s : Finset α) :
    Fintype.card {x : α // x ∉ s} = Fintype.card α - s.card := by
  simp [Fintype.card_subtype_compl]

theorem tha_card_altOff (s : Finset α) (hs : 2 ≤ Fintype.card α - s.card) :
    Nat.card (tha_altOff s) = (Fintype.card α - s.card).factorial / 2 := by
  have : Nontrivial {x : α // x ∉ s} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [tha_card_compl s]; omega)
  rw [Subgroup.card_map_of_injective Perm.ofSubtype_injective, Nat.card_eq_fintype_card,
    card_alternatingGroup, tha_card_compl s]

theorem tha_isSimpleGroup_altOff (s : Finset α)
    (hs : 5 ≤ Fintype.card α - s.card ∨ Fintype.card α - s.card = 3) :
    IsSimpleGroup (tha_altOff s) := by
  rcases hs with hs | hs
  · have h1 : IsSimpleGroup (alternatingGroup {x : α // x ∉ s}) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, tha_card_compl s]; exact hs)
    exact (MulEquiv.isSimpleGroup_congr
      (Subgroup.equivMapOfInjective _ _ Perm.ofSubtype_injective)).mp h1
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine isSimpleGroup_of_prime_card (p := 3) ?_
    rw [tha_card_altOff s (by omega), hs]
    decide

end AltOff

section Alt

variable {n p : ℕ}

theorem tha_conj_mem_centralizer {G : Type*} [Group G] {d g : G} (hg : Commute g d) (h : G) :
    h ∈ Subgroup.centralizer ({d} : Set G) ↔
      g * h * g⁻¹ ∈ Subgroup.centralizer ({d} : Set G) := by
  have hd : g * d * g⁻¹ = d := by rw [hg.eq, mul_inv_cancel_right]
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  conv_rhs => rw [← hd]
  exact (Commute.conj_iff g).symm

theorem tha_signalizer_eq_bot (hp : p.Prime) (hp2 : p ≠ 2) (h2p : 2 * p ≤ n) (hm : n - p ≠ 4)
    {D : Subgroup (alternatingGroup (Fin n))} {d : alternatingGroup (Fin n)}
    {O₁ : Finset (Fin n)} (h₁ : O₁.card = p) (hd : ∀ z, (d : Perm (Fin n)) z ≠ z ↔ z ∈ O₁)
    (hdp : d ^ p = 1) {O : Subgroup (alternatingGroup (Fin n))} (hO : IsPSignalizer p D d O) :
    O = ⊥ := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hcardc : Fintype.card (Fin n) - O₁.card = n - p := by rw [Fintype.card_fin, h₁]
  have hdp' : (d : Perm (Fin n)) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hdp, Subgroup.coe_one]
  have hOfix : ∀ g ∈ O, ∀ w ∈ O₁, (g : Perm (Fin n)) w = w := by
    intro g hg
    have hgd : Commute (g : Perm (Fin n)) (d : Perm (Fin n)) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hO.le_centralizer hg))
    have hN : (g : Perm (Fin n)) ^ Nat.card O = 1 := by
      rw [← Subgroup.coe_pow,
        orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard O hg), Subgroup.coe_one]
    exact tha_fix_of_commute hp h₁ hd hdp' hgd hN hO.coprime.symm
  have hOB : O.map (alternatingGroup (Fin n)).subtype ≤ tha_altOff O₁ := by
    rintro _ ⟨g, hg, rfl⟩
    exact tha_mem_altOff (hOfix g hg) (Perm.mem_alternatingGroup.mp g.2)
  have hBC : ∀ b ∈ tha_altOff O₁, ∃ b' : alternatingGroup (Fin n),
      b' ∈ Subgroup.centralizer ({d} : Set (alternatingGroup (Fin n))) ∧
        (b' : Perm (Fin n)) = b := by
    intro b hb
    refine ⟨⟨b, Perm.mem_alternatingGroup.mpr (tha_sign_of_mem_altOff hb)⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (tha_commute_of_fix hd (fun w hw => tha_apply_eq_of_mem_altOff hb hw)).eq
  have hsimple : IsSimpleGroup (tha_altOff O₁) :=
    tha_isSimpleGroup_altOff O₁ (by rw [hcardc]; omega)
  have hnormal :
      ((O.map (alternatingGroup (Fin n)).subtype).subgroupOf (tha_altOff O₁)).Normal := by
    constructor
    intro y hy g
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    obtain ⟨o, ho, hoy⟩ := hy
    have hoy' : (o : Perm (Fin n)) = y := hoy
    obtain ⟨g', hg', hgg'⟩ := hBC g g.2
    refine ⟨g' * o * g'⁻¹, (Subgroup.mem_normalizer_iff.mp (hO.normal hg') o).mp ho, ?_⟩
    simp [hoy', hgg']
  have hpB : p ∣ Nat.card (tha_altOff O₁) := by
    rw [tha_card_altOff O₁ (by rw [hcardc]; omega), hcardc]
    have h1 : p ∣ (n - p).factorial := Nat.dvd_factorial hp.pos (by omega)
    have h2 : 2 ∣ (n - p).factorial := Nat.dvd_factorial two_pos (by omega)
    rw [← Nat.div_mul_cancel h2] at h1
    exact Nat.Coprime.dvd_of_dvd_mul_right ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) h1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((O.map (alternatingGroup (Fin n)).subtype).subgroupOf (tha_altOff O₁)) with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    exact (Subgroup.map_eq_bot_iff_of_injective O
      (alternatingGroup (Fin n)).subtype_injective).mp (h.eq_bot_of_le hOB)
  · rw [Subgroup.subgroupOf_eq_top] at h
    exfalso
    have h1 : p ∣ Nat.card O := by
      rw [← Subgroup.card_map_of_injective (f := (alternatingGroup (Fin n)).subtype)
        (alternatingGroup (Fin n)).subtype_injective]
      exact hpB.trans (Subgroup.card_dvd_of_le h)
    exact hp.one_lt.ne' (hO.coprime.eq_one_of_dvd h1)

theorem tha_eq_one_of_mem_of_commute {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    (hp2 : p ≠ 2) {D : Subgroup G} (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {d : G} (hd : d ∈ D)
    (hG : ∀ W : Subgroup G, W ≤ Subgroup.centralizer ({d} : Set G) → p.Coprime (Nat.card W) →
      D ≤ Subgroup.normalizer (W : Set G) → W = ⊥)
    {U : Subgroup G} (hU : IsPGroup 2 U) (hDU : D ≤ Subgroup.normalizer (U : Set G)) {u : G}
    (hu : u ∈ U) (hud : u * d = d * u) : u = 1 := by
  have hW := hG (U ⊓ Subgroup.centralizer {d}) inf_le_right ?_ ?_
  · have h : u ∈ U ⊓ Subgroup.centralizer {d} :=
      ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr hud⟩
    rw [hW] at h
    exact Subgroup.mem_bot.mp h
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hU.to_le inf_le_left)
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← tha_conj_mem_centralizer (hDc g hg d hd) h]
    exact and_congr ((Subgroup.mem_normalizer_iff.mp (hDU hg)) h) Iff.rfl

theorem tha_twoSubgroup_eq_bot (hp : p.Prime) (hp2 : p ≠ 2) (hn3 : n < 3 * p)
    {D : Subgroup (alternatingGroup (Fin n))} (hD : CFSG.Open.IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) {d₁ d₂ : alternatingGroup (Fin n)} (hd₁ : d₁ ∈ D)
    (hd₂ : d₂ ∈ D) {O₁ O₂ : Finset (Fin n)} (h₁ : O₁.card = p) (h₂ : O₂.card = p)
    (hO : Disjoint O₁ O₂) (ha₁ : ∀ z, (d₁ : Perm (Fin n)) z ≠ z ↔ z ∈ O₁)
    (ha₂ : ∀ z, (d₂ : Perm (Fin n)) z ≠ z ↔ z ∈ O₂)
    (hG₁ : ∀ W : Subgroup (alternatingGroup (Fin n)),
      W ≤ Subgroup.centralizer ({d₁} : Set (alternatingGroup (Fin n))) →
      p.Coprime (Nat.card W) → D ≤ Subgroup.normalizer (W : Set (alternatingGroup (Fin n))) →
      W = ⊥)
    (hG₂ : ∀ W : Subgroup (alternatingGroup (Fin n)),
      W ≤ Subgroup.centralizer ({d₂} : Set (alternatingGroup (Fin n))) →
      p.Coprime (Nat.card W) → D ≤ Subgroup.normalizer (W : Set (alternatingGroup (Fin n))) →
      W = ⊥)
    {U : Subgroup (alternatingGroup (Fin n))} (hU : IsPGroup 2 U)
    (hDU : D ≤ Subgroup.normalizer (U : Set (alternatingGroup (Fin n)))) : U = ⊥ := by
  have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    have := hD.1
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : D) ⟨y, hy⟩)
  have hU' : ∀ σ ∈ U.map (alternatingGroup (Fin n)).subtype, ∃ e : ℕ, σ ^ 2 ^ e = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨e, he⟩ := hU ⟨v, hv⟩
    refine ⟨e, ?_⟩
    have h1 : v ^ 2 ^ e = 1 := by
      have := congrArg Subtype.val he
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [← map_pow, h1, map_one]
  have haU : ∀ d ∈ D, ∀ σ ∈ U.map (alternatingGroup (Fin n)).subtype,
      (d : Perm (Fin n)) * σ * (d : Perm (Fin n))⁻¹ ∈ U.map (alternatingGroup (Fin n)).subtype := by
    rintro d hd _ ⟨v, hv, rfl⟩
    exact ⟨d * v * d⁻¹, (Subgroup.mem_normalizer_iff.mp (hDU hd) v).mp hv, by simp⟩
  have hGU : ∀ d ∈ D, (∀ W : Subgroup (alternatingGroup (Fin n)),
      W ≤ Subgroup.centralizer ({d} : Set (alternatingGroup (Fin n))) →
      p.Coprime (Nat.card W) → D ≤ Subgroup.normalizer (W : Set (alternatingGroup (Fin n))) →
      W = ⊥) → ∀ τ ∈ U.map (alternatingGroup (Fin n)).subtype,
        Commute τ (d : Perm (Fin n)) → τ = 1 := by
    rintro d hd hG _ ⟨v, hv, rfl⟩ hτ
    have := tha_eq_one_of_mem_of_commute hp hp2 hDc hd hG hU hDU hv (Subtype.ext hτ)
    simp [this]
  have hEc : ∀ d ∈ D, ∀ g ∈ D.map (alternatingGroup (Fin n)).subtype,
      Commute g (d : Perm (Fin n)) := by
    rintro d hd _ ⟨g, hg, rfl⟩
    exact congrArg Subtype.val (hDc g hg d hd)
  have hcent : ∀ b ∈ D, b ≠ 1 → ∀ u ∈ U, b * u * b⁻¹ = u → u = 1 := by
    intro b hb hb1 u hu hbu
    have hbp : (b : Perm (Fin n)) ^ p = 1 := by
      rw [← Subgroup.coe_pow, hD.2 b hb, Subgroup.coe_one]
    have hub : Commute (u : Perm (Fin n)) (b : Perm (Fin n)) := by
      have h1 : b * u = u * b := by rw [← mul_inv_eq_iff_eq_mul, hbu]
      exact congrArg Subtype.val h1.symm
    have huU : (u : Perm (Fin n)) ∈ U.map (alternatingGroup (Fin n)).subtype := ⟨u, hu, rfl⟩
    suffices (u : Perm (Fin n)) = 1 from Subtype.ext this
    by_cases hz₁ : ∃ z ∈ O₁, (b : Perm (Fin n)) z ≠ z
    · obtain ⟨z, hz, hbz⟩ := hz₁
      exact tha_eq_one_of_commute hp hp2 h₁ ha₁ hU' (haU d₁ hd₁) (hGU d₁ hd₁ hG₁) hbp
        (congrArg Subtype.val (hDc b hb d₁ hd₁)) hz hbz huU hub
    by_cases hz₂ : ∃ z ∈ O₂, (b : Perm (Fin n)) z ≠ z
    · obtain ⟨z, hz, hbz⟩ := hz₂
      exact tha_eq_one_of_commute hp hp2 h₂ ha₂ hU' (haU d₂ hd₂) (hGU d₂ hd₂ hG₂) hbp
        (congrArg Subtype.val (hDc b hb d₂ hd₂)) hz hbz huU hub
    push Not at hz₁ hz₂
    exfalso
    apply hb1
    apply Subtype.ext
    exact tha_eq_one_of_fix hp hp2 hn3
      (by rw [Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective, hDcard])
      h₁ h₂ hO ha₁ ha₂ (hEc d₁ hd₁) (hEc d₂ hd₂) ⟨b, hb, rfl⟩ hz₁ hz₂
  let _ : MulDistribMulAction D U :=
    MulDistribMulAction.compHom U (U.normalizerMonoidHom.comp (Subgroup.inclusion hDU))
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p D :=
    { toIsMulCommutative := hD.1
      exponent_dvd_p :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hD.2 g g.2) }
  have hpU : ¬ p ∣ Nat.card U := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hgen := SolvableHall.coprime_centralizer_generation (p := p) (A := D) (H := U)
    hDcard.ge hpU
  have hbot : ∀ b : D, b ≠ 1 → fixedPointSubgroup (Subgroup.zpowers b) U = ⊥ := by
    intro b hb
    rw [eq_bot_iff]
    intro y hy
    rw [SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
    rw [Subgroup.mem_bot]
    have h1 : (b : alternatingGroup (Fin n)) * y * (b : alternatingGroup (Fin n))⁻¹ = y :=
      congrArg Subtype.val hy
    exact Subtype.ext (hcent b b.2 (fun h => hb (Subtype.ext h)) y y.2 h1)
  have htop : (⊤ : Subgroup U) = ⊥ := by
    rw [← hgen]
    exact iSup₂_eq_bot.mpr hbot
  rw [eq_bot_iff]
  intro u hu
  have h : (⟨u, hu⟩ : U) ∈ (⊤ : Subgroup U) := Subgroup.mem_top _
  rw [htop, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h)

end Alt

open CFSG.Open Equiv Subgroup in
theorem alternating_signalizer_case {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn5 : 5 ≤ n)
    (hn3 : n < 3 * p) (D : Subgroup (alternatingGroup (Fin n))) (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2)
    (hsig : ∀ d ∈ D, d ≠ 1 → ∃ O : Subgroup (alternatingGroup (Fin n)), IsPSignalizer p D d O)
    (hjoin : p ∣ Nat.card (invariantTwoJoinIn D (⊤ : Subgroup (alternatingGroup (Fin n))))) :
    p = 3 ∧ n = 7 := by
  have _ := hn5
  have hE : IsElemAbelian p (D.map (alternatingGroup (Fin n)).subtype) := by
    have := hD.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨x, hx, hax⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨z, hz, hbz⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      change (a : Perm (Fin n)) * b = b * a
      rw [← hax, ← hbz, ← map_mul, ← map_mul]
      exact congrArg (fun w : D => (alternatingGroup (Fin n)).subtype w)
        (mul_comm' (⟨x, hx⟩ : D) ⟨z, hz⟩)
    · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      rw [← map_pow, hD.2 x hx, map_one]
  have hEcard : Nat.card (D.map (alternatingGroup (Fin n)).subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective, hDcard]
  obtain ⟨a₁, ha₁E, a₂, ha₂E, O₁, O₂, h₁, h₂, hO, ha₁, ha₂⟩ :=
    AGLEmbeddingD2.exists_cycles_of_isElemAbelian hp hp2 hn3 hE hEcard
  obtain ⟨d₁, hd₁, rfl⟩ := Subgroup.mem_map.mp ha₁E
  obtain ⟨d₂, hd₂, rfl⟩ := Subgroup.mem_map.mp ha₂E
  have h2p : 2 * p ≤ n := by
    have := Finset.card_le_univ (O₁ ∪ O₂)
    rw [Finset.card_union_of_disjoint hO, h₁, h₂, Fintype.card_fin] at this
    omega
  by_contra hne
  have hm : n - p ≠ 4 := by
    intro h
    apply hne
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    have h4 : p ≤ 4 := by omega
    interval_cases p
    · omega
    · exact absurd hp (by decide)
  have hG : ∀ d ∈ D, ∀ O : Finset (Fin n), O.card = p →
      (∀ z, (d : Perm (Fin n)) z ≠ z ↔ z ∈ O) → ∀ W : Subgroup (alternatingGroup (Fin n)),
        W ≤ centralizer ({d} : Set (alternatingGroup (Fin n))) → p.Coprime (Nat.card W) →
        D ≤ normalizer (W : Set (alternatingGroup (Fin n))) → W = ⊥ := by
    intro d hd O hOc hdO W hW1 hW2 hW3
    have hd1 : d ≠ 1 := by
      obtain ⟨z, hz⟩ : O.Nonempty := Finset.card_pos.mp (hOc ▸ hp.pos)
      intro h
      apply (hdO z).mpr hz
      rw [h]
      rfl
    obtain ⟨S, hS⟩ := hsig d hd hd1
    have hS0 := tha_signalizer_eq_bot hp hp2 h2p hm hOc hdO (hD.2 d hd) hS
    exact le_bot_iff.mp (hS0 ▸ hS.le W hW1 hW2 hW3)
  have hjoin_bot : invariantTwoJoinIn D (⊤ : Subgroup (alternatingGroup (Fin n))) = ⊥ :=
    le_bot_iff.mp (invariantTwoJoinIn_le_of_forall fun X _ hX hDX => le_bot_iff.mpr
      (tha_twoSubgroup_eq_bot hp hp2 hn3 hD hDcard hd₁ hd₂ h₁ h₂ hO ha₁ ha₂
        (hG d₁ hd₁ O₁ h₁ ha₁) (hG d₂ hd₂ O₂ h₂ ha₂) hX hDX))
  rw [hjoin_bot, Subgroup.card_bot] at hjoin
  exact hp.one_lt.ne' (Nat.dvd_one.mp hjoin)

end CFSG.LocalAnalysis.RankThreeTheoremC
