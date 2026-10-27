module

import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8

section Finite

variable {G : Type} [Group G] [Finite G]

theorem glaPLayer_eq_of_isSimple_normal_commutator_le {p : ℕ} (hp : p.Prime) {H S : Subgroup G}
    (hSH : S ≤ H) (hSn : ∀ g ∈ H, ∀ s ∈ S, g * s * g⁻¹ ∈ S) (hS : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hpS : p ∣ Nat.card ↥S) (hc : ⁅H, H⁆ ≤ S) :
    GLAPLayer p H = S := by
  haveI := hS
  have hn : (S.subgroupOf H).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hSn g.1 g.2 x hx⟩
  have hcomp : GLAPComponent p H S :=
    GL83.PiGen.glaPComponent_of_normal_simple hp hSH hn hnab hpS
  unfold GLAPLayer
  refine le_antisymm (sSup_le fun J hJ => ?_) (le_sSup hcomp)
  have hJ' : GLAPComponent p H J := hJ
  rw [← GLTheoremB.glaPComponent_perfect hJ']
  exact (Subgroup.commutator_mono hJ'.1 hJ'.1).trans hc

theorem glaPLayer_eq_of_unique_glaPComponent {p : ℕ} {H S : Subgroup G}
    (hS : GLAPComponent p H S) (huniq : ∀ J, GLAPComponent p H J → J = S) :
    GLAPLayer p H = S := by
  unfold GLAPLayer
  exact le_antisymm (sSup_le fun J hJ => (huniq J hJ).le) (le_sSup hS)

theorem isTypeWithCenter_of_isSimple {p : ℕ} (hp : p.Prime) {J : Subgroup G}
    (hJ : IsSimpleGroup ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a) (hpJ : p ∣ Nat.card ↥J)
    {Q : TauCeti.CFSGIndex → Prop} (hQ : catalogIs ↥J Q) : IsTypeWithCenter p J Q 1 := by
  haveI := hJ
  haveI : Fact p.Prime := ⟨hp⟩
  have hcore : GLAPPrimeCore p ↥J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥J) with h | h
    · exact h
    · exfalso
      have hc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥J)) := CFSG.pPrimeCore_coprime_card
      rw [h, Subgroup.card_top] at hc
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp hc hpJ
  have hZ : Subgroup.center ↥J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥J) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center ↥J := by rw [h]; trivial
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  let e : PQuot p J ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have hZq : Subgroup.center (PQuot p J) = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, hZ, Subgroup.map_bot]
  let e' : PSimple p J ≃* ↥J :=
    ((QuotientGroup.quotientMulEquivOfEq hZq).trans QuotientGroup.quotientBot).trans e
  obtain ⟨i, hi, ⟨f⟩⟩ := hQ
  exact ⟨⟨i, hi, ⟨e'.trans f⟩⟩, by rw [hZq, Subgroup.card_bot]⟩

theorem le_centralizer_of_normal_two_simple {H N K : Subgroup G} (hNH : N ≤ H) (hKH : K ≤ H)
    (hNn : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hKn : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hN : IsPGroup 2 ↥N) (hK : IsSimpleGroup ↥K) (hK2 : ¬ IsPGroup 2 ↥K) :
    N ≤ Subgroup.centralizer (K : Set G) := by
  haveI := hK
  have hnorm : (N.subgroupOf K).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hNn g.1 (hKH g.2) x hx⟩
  have hdisj : Disjoint N K := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf K) with h | h
    · exact Subgroup.subgroupOf_eq_bot.1 h
    · exact absurd (hN.to_le (Subgroup.subgroupOf_eq_top.1 h)) hK2
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hN' : n * k * n⁻¹ * k⁻¹ ∈ N := by
    have h := N.mul_mem hn (hNn k (hKH hk) n⁻¹ (N.inv_mem hn))
    rwa [← mul_assoc, ← mul_assoc] at h
  have hK' : n * k * n⁻¹ * k⁻¹ ∈ K := K.mul_mem (hKn n (hNH hn) k hk) (K.inv_mem hk)
  have h1 : n * k * n⁻¹ * k⁻¹ = 1 := Subgroup.disjoint_def.1 hdisj hN' hK'
  calc k * n = (n * k * n⁻¹ * k⁻¹)⁻¹ * (n * k) := by group
    _ = n * k := by rw [h1, inv_one, one_mul]

theorem isElemAbelian_closure_three {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (hind : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 → a ^ i * b ^ j * c ^ k = 1 →
      i = 0 ∧ j = 0 ∧ k = 0) :
    IsElemAbelian 3 (Subgroup.closure {a, b, c}) ∧
      Nat.card (Subgroup.closure {a, b, c}) = 3 ^ 3 := by
  have hmul : ∀ i j k i' j' k' : ℕ, a ^ i * b ^ j * c ^ k * (a ^ i' * b ^ j' * c ^ k') =
      a ^ (i + i') * b ^ (j + j') * c ^ (k + k') := by
    intro i j k i' j' k'
    simp only [pow_add, mul_assoc]
    rw [((hac.pow_pow i' k).symm).left_comm, ((hab.pow_pow i' j).symm).left_comm,
      ((hbc.pow_pow j' k).symm).left_comm]
  have hone : ∀ i j k : ℕ, a ^ (3 * i) * b ^ (3 * j) * c ^ (3 * k) = 1 := by
    intro i j k
    simp [pow_mul, ha, hb, hc]
  have hred : ∀ i j k : ℕ, a ^ i * b ^ j * c ^ k = a ^ (i % 3) * b ^ (j % 3) * c ^ (k % 3) := by
    intro i j k
    rw [pow_eq_pow_mod i ha, pow_eq_pow_mod j hb, pow_eq_pow_mod k hc]
  have hrep : ∀ g ∈ Subgroup.closure ({a, b, c} : Set G),
      ∃ i j k : ℕ, g = a ^ i * b ^ j * c ^ k := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
    | one => exact ⟨0, 0, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, j, k, rfl⟩ := hx
      obtain ⟨i', j', k', rfl⟩ := hy
      exact ⟨i + i', j + j', k + k', hmul i j k i' j' k'⟩
    | inv x _ hx =>
      obtain ⟨i, j, k, rfl⟩ := hx
      refine ⟨2 * i, 2 * j, 2 * k, inv_eq_of_mul_eq_one_right ?_⟩
      rw [hmul, show i + 2 * i = 3 * i by ring, show j + 2 * j = 3 * j by ring,
        show k + 2 * k = 3 * k by ring, hone]
  have hcomm : ∀ x ∈ Subgroup.closure ({a, b, c} : Set G),
      ∀ y ∈ Subgroup.closure ({a, b, c} : Set G), x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, j, k, rfl⟩ := hrep x hx
    obtain ⟨i', j', k', rfl⟩ := hrep y hy
    rw [hmul, hmul, Nat.add_comm i, Nat.add_comm j, Nat.add_comm k]
  refine ⟨⟨isMulCommutative_iff.2 fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2), ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, j, k, rfl⟩ := hrep x hx
    rw [pow_three, hmul, hmul, show i + (i + i) = 3 * i by ring,
      show j + (j + j) = 3 * j by ring, show k + (k + k) = 3 * k by ring, hone]
  · have hmem : ∀ i j k : ℕ, a ^ i * b ^ j * c ^ k ∈ Subgroup.closure ({a, b, c} : Set G) := by
      intro i j k
      have ha' : a ∈ Subgroup.closure ({a, b, c} : Set G) := Subgroup.subset_closure (by simp)
      have hb' : b ∈ Subgroup.closure ({a, b, c} : Set G) := Subgroup.subset_closure (by simp)
      have hc' : c ∈ Subgroup.closure ({a, b, c} : Set G) := Subgroup.subset_closure (by simp)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ha' i)
        (Subgroup.pow_mem _ hb' j)) (Subgroup.pow_mem _ hc' k)
    let f : Fin 3 × Fin 3 × Fin 3 → Subgroup.closure ({a, b, c} : Set G) :=
      fun t => ⟨a ^ (t.1 : ℕ) * b ^ (t.2.1 : ℕ) * c ^ (t.2.2 : ℕ), hmem _ _ _⟩
    have hinj : Function.Injective f := by
      rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
      have h' : a ^ (i : ℕ) * b ^ (j : ℕ) * c ^ (k : ℕ) =
          a ^ (i' : ℕ) * b ^ (j' : ℕ) * c ^ (k' : ℕ) := congrArg Subtype.val h
      have h1 : a ^ (((i : ℕ) + 2 * i') % 3) * b ^ (((j : ℕ) + 2 * j') % 3) *
          c ^ (((k : ℕ) + 2 * k') % 3) = 1 := by
        rw [← hred, ← hmul, h', hmul, show (i' : ℕ) + 2 * i' = 3 * i' by ring,
          show (j' : ℕ) + 2 * j' = 3 * j' by ring, show (k' : ℕ) + 2 * k' = 3 * k' by ring, hone]
      obtain ⟨hi, hj, hk⟩ := hind _ _ _ (Nat.mod_lt _ (by norm_num))
        (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1
      have := i.isLt; have := i'.isLt; have := j.isLt; have := j'.isLt
      have := k.isLt; have := k'.isLt
      have hi' : (i : ℕ) = i' := by omega
      have hj' : (j : ℕ) = j' := by omega
      have hk' : (k : ℕ) = k' := by omega
      simp only [Prod.mk.injEq]
      exact ⟨Fin.ext hi', Fin.ext hj', Fin.ext hk'⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨i, j, k, rfl⟩ := hrep g hg
      refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩,
        ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩), Subtype.ext ?_⟩
      exact (hred i j k).symm
    rw [← Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩]
    simp [Nat.card_eq_fintype_card]

end Finite

open scoped Pointwise commutatorElement in
theorem commutator_le_of_le_sup_of_commute {G : Type*} [Group G] {H S A : Subgroup G}
    (hHSA : H ≤ S ⊔ A) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAS : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S) : ⁅H, H⁆ ≤ S := by
  have hAN : A ≤ Subgroup.normalizer (S : Set G) := fun a ha =>
    Subgroup.mem_normalizer_iff.2 fun s => ⟨fun hs => hAS a ha s hs, fun hs => by
      have h := hAS a⁻¹ (A.inv_mem ha) _ hs
      have e : a⁻¹ * (a * s * a⁻¹) * a⁻¹⁻¹ = s := by group
      rwa [e] at h⟩
  have hsup : ((S ⊔ A : Subgroup G) : Set G) = (A : Set G) * (S : Set G) := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right A S hAN
  refine (Subgroup.commutator_mono hHSA hHSA).trans ?_
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hx' : x ∈ ((S ⊔ A : Subgroup G) : Set G) := hx
  have hy' : y ∈ ((S ⊔ A : Subgroup G) : Set G) := hy
  rw [hsup] at hx' hy'
  obtain ⟨a, ha, s, hs, rfl⟩ := hx'
  obtain ⟨a', ha', s', hs', rfl⟩ := hy'
  have h1 : a * s * a⁻¹ ∈ S := hAS a ha s hs
  have h2 : (a * a') * (s' * s⁻¹) * (a * a')⁻¹ ∈ S :=
    hAS _ (A.mul_mem ha ha') _ (S.mul_mem hs' (S.inv_mem hs))
  have h3 : a' * s'⁻¹ * a'⁻¹ ∈ S := hAS a' ha' _ (S.inv_mem hs')
  have hcomm : a * a' = a' * a := hA a ha a' ha'
  have heq : ⁅a * s, a' * s'⁆ =
      a * s * a⁻¹ * ((a * a') * (s' * s⁻¹) * (a * a')⁻¹) * (a' * s'⁻¹ * a'⁻¹) := by
    have e : a * a' * a⁻¹ = a' := by rw [hcomm, mul_inv_cancel_right]
    calc ⁅a * s, a' * s'⁆ = a * s * a' * s' * s⁻¹ * a⁻¹ * s'⁻¹ * a'⁻¹ := by
          rw [commutatorElement_def]; group
      _ = a * s * a⁻¹ * ((a * a') * (s' * s⁻¹) * (a * a')⁻¹) * (a * a' * a⁻¹ * s'⁻¹ * a'⁻¹) := by
          group
      _ = a * s * a⁻¹ * ((a * a') * (s' * s⁻¹) * (a * a')⁻¹) * (a' * s'⁻¹ * a'⁻¹) := by
          rw [e]
  rw [heq]
  exact S.mul_mem (S.mul_mem h1 h2) h3

theorem nonempty_mulEquiv_alternatingGroup_six {n : ℕ} {a b : Equiv.Perm (Fin n)}
    (o : Fin 6 → Fin n) (ho : Function.Injective o) {σa σb : Equiv.Perm (Fin 6)}
    (ha : ∀ j, a (o j) = o (σa j)) (hb : ∀ j, b (o j) = o (σb j))
    (hσa : σa ∈ alternatingGroup (Fin 6)) (hσb : σb ∈ alternatingGroup (Fin 6))
    (hfix : ∀ g ∈ Subgroup.closure {a, b}, (∀ j, g (o j) = o j) → g = 1)
    (hcard : Nat.card (Subgroup.closure {a, b}) = 360) :
    Nonempty (↥(Subgroup.closure {a, b}) ≃* alternatingGroup (Fin 6)) := by
  set D : Subgroup (Equiv.Perm (Fin n) × Equiv.Perm (Fin 6)) :=
    Subgroup.closure {(a, σa), (b, σb)} with hDdef
  have hD : ∀ x ∈ D, ∀ j, x.1 (o j) = o (x.2 j) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    | one => exact fun j => rfl
    | mul x y _ _ hx hy =>
      intro j
      simp only [Prod.fst_mul, Prod.snd_mul, Equiv.Perm.coe_mul, Function.comp_apply, hy, hx]
    | inv x _ hx =>
      intro j
      simp only [Prod.fst_inv, Prod.snd_inv]
      rw [Equiv.Perm.inv_eq_iff_eq, hx]
      simp
  have hfst : D.map (MonoidHom.fst _ _) = Subgroup.closure {a, b} := by
    rw [hDdef, MonoidHom.map_closure, Set.image_pair]
    rfl
  have hsnd : D.map (MonoidHom.snd _ _) = Subgroup.closure {σa, σb} := by
    rw [hDdef, MonoidHom.map_closure, Set.image_pair]
    rfl
  set f₁ : ↥D →* Equiv.Perm (Fin n) := (MonoidHom.fst _ _).comp D.subtype with hf₁
  set f₂ : ↥D →* Equiv.Perm (Fin 6) := (MonoidHom.snd _ _).comp D.subtype with hf₂
  have hr₁ : f₁.range = Subgroup.closure {a, b} := by
    rw [hf₁, MonoidHom.range_comp, Subgroup.range_subtype, hfst]
  have hr₂ : f₂.range = Subgroup.closure {σa, σb} := by
    rw [hf₂, MonoidHom.range_comp, Subgroup.range_subtype, hsnd]
  have hinj₁ : Function.Injective f₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : (x : Equiv.Perm (Fin n) × Equiv.Perm (Fin 6)).1 = 1 := hx
    have h2 : (x : Equiv.Perm (Fin n) × Equiv.Perm (Fin 6)).2 = 1 := by
      ext j
      have := hD x.1 x.2 j
      rw [h1] at this
      exact congrArg Fin.val (ho this).symm
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Prod.ext h1 h2)
  have hinj₂ : Function.Injective f₂ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h2 : (x : Equiv.Perm (Fin n) × Equiv.Perm (Fin 6)).2 = 1 := hx
    have hmem : (x : Equiv.Perm (Fin n) × Equiv.Perm (Fin 6)).1 ∈ Subgroup.closure {a, b} := by
      rw [← hr₁]
      exact ⟨x, rfl⟩
    have h1 : (x : Equiv.Perm (Fin n) × Equiv.Perm (Fin 6)).1 = 1 := by
      refine hfix _ hmem fun j => ?_
      rw [hD x.1 x.2 j, h2]
      rfl
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Prod.ext h1 h2)
  let e₁ : ↥D ≃* ↥(Subgroup.closure {a, b}) :=
    (MonoidHom.ofInjective hinj₁).trans (MulEquiv.subgroupCongr hr₁)
  let e₂ : ↥D ≃* ↥(Subgroup.closure {σa, σb}) :=
    (MonoidHom.ofInjective hinj₂).trans (MulEquiv.subgroupCongr hr₂)
  have hle : Subgroup.closure {σa, σb} ≤ alternatingGroup (Fin 6) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hσa
    · exact hσb
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hcard' : Nat.card (Subgroup.closure {σa, σb}) = 360 := by
    rw [← Nat.card_congr e₂.toEquiv, Nat.card_congr e₁.toEquiv, hcard]
  have heq : Subgroup.closure {σa, σb} = alternatingGroup (Fin 6) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hA6, hcard'])
  exact ⟨(e₁.symm.trans e₂).trans (MulEquiv.subgroupCongr heq)⟩

end CFSG.LocalAnalysis.GLTheoremA.H301
