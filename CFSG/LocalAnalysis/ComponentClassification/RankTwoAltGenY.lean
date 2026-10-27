module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypNF
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltAct
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltC5
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCarmichael

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
  CFSG.Quasithin.SteinbergCB

section Invol

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem cycleType_of_mul_self {σ : Perm α} (h1 : σ ≠ 1) (h2 : σ * σ = 1) (hs : sign σ = 1)
    (h8 : σ.support.card ≤ 8) : σ.cycleType = {2, 2} ∨ σ.cycleType = {2, 2, 2, 2} := by
  have hall : ∀ x ∈ σ.cycleType, x = 2 := by
    intro x hx
    have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h2])
    have h2le := two_le_of_mem_cycleType hx
    have hle := Nat.le_of_dvd (by norm_num) ((dvd_of_mem_cycleType hx).trans hord)
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.mpr hall
  have hk0 : Multiset.card σ.cycleType ≠ 0 := fun h0 => h1 (card_cycleType_eq_zero.mp h0)
  have hsum := sum_cycleType σ
  have hsign := sign_of_cycleType σ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hs, hrep, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  have hev : (Multiset.card σ.cycleType * 2 + Multiset.card σ.cycleType) % 2 = 0 := by
    by_contra hodd
    have hodd' : Odd (Multiset.card σ.cycleType * 2 + Multiset.card σ.cycleType) :=
      Nat.odd_iff.mpr (by omega)
    rw [hodd'.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  have hk : Multiset.card σ.cycleType = 2 ∨ Multiset.card σ.cycleType = 4 := by omega
  rcases hk with hk | hk
  · left
    rw [hrep, hk]
    rfl
  · right
    rw [hrep, hk]
    rfl

theorem cycleType_mul_of_commute {a b : Perm α} (ha : a.cycleType = {2, 2})
    (hb : b.cycleType = {2, 2}) (hab : a * b = b * a) (hne : a ≠ b) :
    (a * b).cycleType = {2, 2} ∨ (a * b).cycleType = {2, 2, 2, 2} := by
  have hinv : ∀ {c : Perm α}, c.cycleType = {2, 2} → c * c = 1 := by
    intro c hc
    have hord : orderOf c = 2 := by
      rw [← lcm_cycleType, hc]
      rfl
    rw [← sq, ← hord, pow_orderOf_eq_one]
  have hsign : ∀ {c : Perm α}, c.cycleType = {2, 2} → sign c = 1 := by
    intro c hc
    rw [sign_of_cycleType, hc]
    rfl
  have hcard : ∀ {c : Perm α}, c.cycleType = {2, 2} → c.support.card = 4 := by
    intro c hc
    rw [← sum_cycleType, hc]
    rfl
  refine cycleType_of_mul_self (fun h => hne ?_) ?_ ?_ ?_
  · calc a = a * (b * b) := by rw [hinv hb, mul_one]
      _ = b := by rw [← mul_assoc, h, one_mul]
  · calc a * b * (a * b) = a * a * (b * b) := by rw [mul_assoc, ← mul_assoc b, ← hab]; group
      _ = 1 := by rw [hinv ha, hinv hb, one_mul]
  · rw [Perm.sign_mul, hsign ha, hsign hb, one_mul]
  · calc (a * b).support.card ≤ (a.support ∪ b.support).card :=
          Finset.card_le_card (support_mul_le a b)
      _ ≤ a.support.card + b.support.card := Finset.card_union_le _ _
      _ = 8 := by rw [hcard ha, hcard hb]

theorem exists_mem_alternatingGroup_conj_eq {s t : Perm α}
    (h : s.cycleType = t.cycleType) (h2 : s * s = 1) (h1 : s ≠ 1) :
    ∃ b ∈ alternatingGroup α, b * s * b⁻¹ = t := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr h)
  obtain ⟨x, hx⟩ : ∃ x, s x ≠ x := by
    by_contra hall
    push Not at hall
    exact h1 (Equiv.ext hall)
  have hss : s (s x) = x := by rw [← Perm.mul_apply, h2, Perm.one_apply]
  have hcomm : swap x (s x) * s = s * swap x (s x) := by
    have h3 := swap_apply_apply s x (s x)
    rw [hss, swap_comm] at h3
    calc swap x (s x) * s = s * swap x (s x) * s⁻¹ * s := by rw [← h3]
      _ = s * swap x (s x) := by group
  by_cases hsc : sign c = 1
  · exact ⟨c, hsc, hc⟩
  · have hsd : sign (swap x (s x)) = -1 := sign_swap hx.symm
    have hsc' : sign c = -1 := by
      rcases Int.units_eq_one_or (sign c) with h' | h'
      · exact absurd h' hsc
      · exact h'
    refine ⟨c * swap x (s x), by rw [mem_alternatingGroup, Perm.sign_mul, hsc', hsd]; rfl, ?_⟩
    calc c * swap x (s x) * s * (c * swap x (s x))⁻¹ =
        c * (swap x (s x) * s * (swap x (s x))⁻¹) * c⁻¹ := by group
      _ = t := by rw [hcomm, mul_inv_cancel_right, hc]

theorem exists_conj_eq_of_cycleType_eq {σ τ : alternatingGroup α}
    (h : (σ : Perm α).cycleType = (τ : Perm α).cycleType) (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    ∃ β : alternatingGroup α, β * σ * β⁻¹ = τ := by
  have h2' : (σ : Perm α) * σ = 1 := by
    rw [← Subgroup.coe_mul, h2]
    rfl
  have h1' : (σ : Perm α) ≠ 1 := fun h' => h1 (Subtype.ext h')
  obtain ⟨b, hb, hbe⟩ := exists_mem_alternatingGroup_conj_eq h h2' h1'
  exact ⟨⟨b, hb⟩, Subtype.ext hbe⟩

theorem cycleType_viaEmbeddingHom' {β : Type*} [Fintype β] [DecidableEq β] (ι : α ↪ β)
    (σ : Perm α) : (viaEmbeddingHom ι σ).cycleType = σ.cycleType := by
  show (Equiv.Perm.viaEmbedding σ ι).cycleType = σ.cycleType
  unfold Equiv.Perm.viaEmbedding
  convert Equiv.Perm.cycleType_extendDomain (Equiv.ofInjective ι.1 ι.2) (g := σ) using 3

end Invol

section Letters

variable {n : ℕ}

theorem cycleType_swap01_swap23 : ((swap 0 1 * swap 2 3 : Perm (Fin 4))).cycleType = {2, 2} := by
  have hc : (swap 0 1 * swap 2 3 : Perm (Fin 4)).support.card = 4 := by decide
  rcases cycleType_of_mul_self (σ := (swap 0 1 * swap 2 3 : Perm (Fin 4))) (by decide) (by decide)
    (by decide) (by rw [hc]; norm_num) with h | h
  · exact h
  · have h' := sum_cycleType (swap 0 1 * swap 2 3 : Perm (Fin 4))
    rw [h, hc] at h'
    simp at h'

theorem swap01_swap23_mem : (swap 0 1 * swap 2 3 : Perm (Fin 4)) ∈ alternatingGroup (Fin 4) :=
  mem_alternatingGroup.mpr (by decide)

@[expose] noncomputable def rootLast (n : ℕ) : alternatingGroup (Fin (n + 4)) :=
  ⟨viaEmbeddingHom (Fin.natAddEmb n) (swap 0 1 * swap 2 3), by
    rw [mem_alternatingGroup, sign_viaEmbeddingHom]
    exact swap01_swap23_mem⟩

@[expose] noncomputable def rootFirst (n : ℕ) : alternatingGroup (Fin (n + 4)) :=
  ⟨viaEmbeddingHom (Fin.castLEEmb (by omega : 4 ≤ n + 4)) (swap 0 1 * swap 2 3), by
    rw [mem_alternatingGroup, sign_viaEmbeddingHom]
    exact swap01_swap23_mem⟩

theorem cycleType_rootLast : ((rootLast n : alternatingGroup (Fin (n + 4))) :
    Perm (Fin (n + 4))).cycleType = {2, 2} := by
  rw [rootLast, cycleType_viaEmbeddingHom', cycleType_swap01_swap23]

theorem cycleType_rootFirst : ((rootFirst n : alternatingGroup (Fin (n + 4))) :
    Perm (Fin (n + 4))).cycleType = {2, 2} := by
  rw [rootFirst, cycleType_viaEmbeddingHom', cycleType_swap01_swap23]

theorem cycleType_rootFirst_mul_rootLast (h4 : 4 ≤ n) :
    ((rootFirst n * rootLast n : alternatingGroup (Fin (n + 4))) :
      Perm (Fin (n + 4))).cycleType = {2, 2, 2, 2} := by
  have hd : Perm.Disjoint (rootFirst n : Perm (Fin (n + 4))) (rootLast n) := by
    intro x
    by_cases hx : (x : ℕ) < 4
    · right
      refine viaEmbeddingHom_apply_of_notMem _ _ ?_
      rintro ⟨i, rfl⟩
      simp only [Fin.natAddEmb_apply, Fin.val_natAdd] at hx
      omega
    · left
      refine viaEmbeddingHom_apply_of_notMem _ _ ?_
      rintro ⟨i, rfl⟩
      exact hx (by simp only [Fin.castLEEmb_apply, Fin.val_castLE]; exact i.2)
  rw [Subgroup.coe_mul, hd.cycleType_mul, cycleType_rootFirst, cycleType_rootLast]
  rfl

theorem rootLast_mul_rootLast : rootLast n * rootLast n = 1 := by
  apply Subtype.ext
  have hord : orderOf ((rootLast n : alternatingGroup (Fin (n + 4))) :
      Perm (Fin (n + 4))) = 2 := by
    rw [← lcm_cycleType, cycleType_rootLast]
    rfl
  rw [Subgroup.coe_mul, ← sq, ← hord, pow_orderOf_eq_one]
  rfl

theorem rootLast_ne_one : rootLast n ≠ 1 := by
  intro h1
  have h2 := cycleType_rootLast (n := n)
  rw [h1] at h2
  simp at h2

theorem mul_self_of_cycleType_two_four {π : alternatingGroup (Fin (n + 4))}
    (hπ : (π : Perm (Fin (n + 4))).cycleType = {2, 2, 2, 2}) : π * π = 1 ∧ π ≠ 1 := by
  refine ⟨Subtype.ext ?_, fun h1 => ?_⟩
  · have hord : orderOf (π : Perm (Fin (n + 4))) = 2 := by
      rw [← lcm_cycleType, hπ]
      rfl
    rw [Subgroup.coe_mul, ← sq, ← hord, pow_orderOf_eq_one]
    rfl
  · rw [h1] at hπ
    simp at hπ

theorem coe_liftA (hn : 6 ≤ n) (z : alternatingGroup (Fin n)) :
    ((liftA hn z : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) =
      viaEmbeddingHom (Fin.castLEEmb (by omega : n ≤ n + 4))
        (tau45 hn * (z : Perm (Fin n)) * (tau45 hn)⁻¹) :=
  rfl

theorem liftA_injective (hn : 6 ≤ n) : Function.Injective (liftA hn) := by
  intro a b h
  have h1 := congrArg (fun x : alternatingGroup (Fin (n + 4)) => (x : Perm (Fin (n + 4)))) h
  simp only [coe_liftA] at h1
  have h2 := viaEmbeddingHom_injective _ h1
  exact Subtype.ext (by simpa using h2)

theorem commute_castLE_natAdd (x : Perm (Fin n)) (y : Perm (Fin 4)) :
    viaEmbeddingHom (Fin.castLEEmb (by omega : n ≤ n + 4)) x *
        viaEmbeddingHom (Fin.natAddEmb n) y =
      viaEmbeddingHom (Fin.natAddEmb n) y *
        viaEmbeddingHom (Fin.castLEEmb (by omega : n ≤ n + 4)) x := by
  refine viaEmbeddingHom_mul_comm _ (τ := 1) (fun a => ?_) (by rw [mul_one, one_mul])
  rw [Perm.one_apply]
  refine viaEmbeddingHom_apply_of_notMem _ _ ?_
  rintro ⟨i, hi⟩
  have h1 := congrArg Fin.val hi
  simp only [Fin.natAddEmb_apply, Fin.val_natAdd, Fin.castLEEmb_apply, Fin.val_castLE] at h1
  have := a.2
  omega

@[expose] noncomputable def liftNat (n : ℕ) :
    alternatingGroup (Fin n) →* alternatingGroup (Fin (n + 4)) :=
  ((viaEmbeddingHom (Fin.castLEEmb (by omega : n ≤ n + 4))).comp
    (alternatingGroup (Fin n)).subtype).codRestrict (alternatingGroup (Fin (n + 4))) fun z => by
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [mem_alternatingGroup, sign_viaEmbeddingHom]
      exact mem_alternatingGroup.mp z.2

theorem coe_liftNat (z : alternatingGroup (Fin n)) :
    ((liftNat n z : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) =
      viaEmbeddingHom (Fin.castLEEmb (by omega : n ≤ n + 4)) (z : Perm (Fin n)) :=
  rfl

theorem liftNat_injective : Function.Injective (liftNat n) := by
  intro a b h
  have h1 := congrArg (fun x : alternatingGroup (Fin (n + 4)) => (x : Perm (Fin (n + 4)))) h
  simp only [coe_liftNat] at h1
  exact Subtype.ext (viaEmbeddingHom_injective _ h1)

theorem commute_rootLast_liftNat (z : alternatingGroup (Fin n)) :
    rootLast n * liftNat n z = liftNat n z * rootLast n := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_liftNat, rootLast]
  exact (commute_castLE_natAdd _ _).symm

theorem liftA_eq_liftNat (hn : 6 ≤ n) (z : alternatingGroup (Fin n)) :
    liftA hn z = liftNat n (MulAut.conj (⟨tau45 hn, tau45_mem hn⟩ : alternatingGroup (Fin n)) z) :=
  rfl

theorem range_liftA_eq_range_liftNat {G : Type*} [Group G] (hn : 6 ≤ n)
    (Φ : alternatingGroup (Fin (n + 4)) →* G) :
    (Φ.comp (liftA hn)).range = (Φ.comp (liftNat n)).range := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, liftA_eq_liftNat]⟩
  · rintro ⟨z, rfl⟩
    refine ⟨(MulAut.conj (⟨tau45 hn, tau45_mem hn⟩ : alternatingGroup (Fin n))).symm z, ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, liftA_eq_liftNat, MulEquiv.apply_symm_apply]

end Letters

section Sylow

variable {G : Type} [Group G] [Finite G]

open scoped Pointwise in
theorem exists_conj_mem_of_isSylowOf_two {K P : Subgroup G} (hP : IsSylowOf 2 P K) {x : G}
    (hx : x ∈ K) {e : ℕ} (he : orderOf x = 2 ^ e) : ∃ c ∈ K, c * x * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := hP
  have hZ : IsPGroup 2 (zpowers (⟨x, hx⟩ : K)) :=
    IsPGroup.of_card (n := e) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, he])
  obtain ⟨S', hS'⟩ := hZ.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq K S' S
  have hmem : m * ⟨x, hx⟩ * m⁻¹ ∈ (S : Subgroup K) := by
    rw [← hm, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (mem_zpowers _))
  exact ⟨m, m.2, ⟨_, hmem, rfl⟩⟩

end Sylow

section Act

variable {G : Type} [Group G] {N : ℕ} (hN : 7 ≤ N) {Φ : alternatingGroup (Fin N) →* G}
  (hΦ : Function.Injective Φ)

noncomputable abbrev actPermY : normalizer (Φ.range : Set G) →* Perm (Fin N) :=
  actPerm (MonoidHom.ofInjective hΦ).symm (Or.inr hN)

theorem actPermY_spec (k : normalizer (Φ.range : Set G)) (π : alternatingGroup (Fin N)) :
    Φ (conjPerm N (actPermY hN hΦ k) π) = (k : G) * Φ π * (k : G)⁻¹ := by
  have h := actPerm_spec (MonoidHom.ofInjective hΦ).symm (Or.inr hN) k
    (MonoidHom.ofInjective hΦ π)
  rw [MulEquiv.symm_apply_apply] at h
  have h2 : (MonoidHom.ofInjective hΦ).symm ⟨(k : G) * (MonoidHom.ofInjective hΦ π : G) *
      (k : G)⁻¹, (mem_normalizer_iff.mp k.2 _).mp (MonoidHom.ofInjective hΦ π).2⟩ =
      conjPerm N (actPermY hN hΦ k) π :=
    Subtype.ext (by rw [h, conjPerm_apply])
  have h3 := congrArg (fun x => ((MonoidHom.ofInjective hΦ x : Φ.range) : G)) h2
  simp only [MulEquiv.apply_symm_apply, MonoidHom.ofInjective_apply] at h3
  exact h3.symm

theorem actPermY_phi (π : alternatingGroup (Fin N)) :
    actPermY hN hΦ ⟨Φ π, le_normalizer ⟨π, rfl⟩⟩ = π := by
  apply conjPerm_injective (by omega : 4 ≤ N)
  ext β : 1
  apply Subtype.ext
  have h1 := actPermY_spec hN hΦ ⟨Φ π, le_normalizer ⟨π, rfl⟩⟩ β
  rw [← map_inv, ← map_mul, ← map_mul] at h1
  rw [hΦ h1, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, conjPerm_apply]

theorem mem_sup_of_sign {k : G} (hk : k ∈ normalizer (Φ.range : Set G))
    (hs : sign (actPermY hN hΦ ⟨k, hk⟩) = 1) :
    k ∈ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  set π : alternatingGroup (Fin N) := ⟨actPermY hN hΦ ⟨k, hk⟩, hs⟩
  have hc : (Φ π)⁻¹ * k ∈ centralizer (Φ.range : Set G) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨β, rfl⟩
    have h1 := actPermY_spec hN hΦ ⟨k, hk⟩ β
    have h2 : conjPerm N (actPermY hN hΦ ⟨k, hk⟩) β = π * β * π⁻¹ :=
      Subtype.ext (by rw [conjPerm_apply]; rfl)
    rw [h2, map_mul, map_mul, map_inv] at h1
    calc Φ β * ((Φ π)⁻¹ * k) = (Φ π)⁻¹ * (Φ π * Φ β * (Φ π)⁻¹) * k := by group
      _ = (Φ π)⁻¹ * (k * Φ β * k⁻¹) * k := by rw [h1]
      _ = (Φ π)⁻¹ * k * Φ β := by group
  have hπY : Φ π ∈ Φ.range := ⟨π, rfl⟩
  have h := mul_mem_sup hπY hc
  rwa [mul_inv_cancel_left] at h

end Act

theorem map_rootLast_mul_self {G : Type*} [Group G] {n : ℕ}
    (Φ : alternatingGroup (Fin (n + 4)) →* G) : Φ (rootLast n) * Φ (rootLast n) = 1 := by
  rw [← map_mul, rootLast_mul_rootLast, map_one]

variable {G : Type} [Group G] [Finite G]

structure AltGenCore (A R T : Subgroup G) (g : G) (n : ℕ)
    (Φ : alternatingGroup (Fin (n + 4)) →* G) : Prop where
  five_le : 5 ≤ n
  hyp : RankTwoHypNF G A
  oddCore_eq_bot : standardComponentOddCore G = ⊥
  sec3 : Sec3 A R T g
  T_le : T ≤ A
  R_le : R ≤ rightConjugate A g
  injective : Function.Injective Φ
  range_eq : Φ.range = A ⊔ rightConjugate A g
  range_liftNat : (Φ.comp (liftNat n)).range = A

structure AltGenSetting (A R T : Subgroup G) (g : G) (n : ℕ)
    (Φ : alternatingGroup (Fin (n + 4)) →* G) : Prop extends AltGenCore A R T g n Φ where
  six_le : 6 ≤ n
  range_liftA : (Φ.comp (liftA six_le)).range = A
  five_le := Nat.le_of_succ_le six_le
  range_liftNat := (range_liftA_eq_range_liftNat six_le Φ).symm.trans range_liftA

namespace AltGenCore

variable {A R T : Subgroup G} {g : G} {n : ℕ} {Φ : alternatingGroup (Fin (n + 4)) →* G}
  (s : AltGenCore A R T g n Φ)
include s

theorem le_range : A ≤ Φ.range := s.range_eq ▸ le_sup_left

theorem le_range' : rightConjugate A g ≤ Φ.range := s.range_eq ▸ le_sup_right

theorem exists_liftNat_eq {a : G} (ha : a ∈ A) : ∃ z, Φ (liftNat n z) = a := by
  rw [← s.range_liftNat] at ha
  exact ha

theorem liftNat_mem (z : alternatingGroup (Fin n)) : Φ (liftNat n z) ∈ A := by
  have h : Φ (liftNat n z) ∈ (Φ.comp (liftNat n)).range := ⟨z, rfl⟩
  rwa [s.range_liftNat] at h

@[expose] noncomputable def psiNat : alternatingGroup (Fin n) ≃* A :=
  (MonoidHom.ofInjective (f := Φ.comp (liftNat n))
    (s.injective.comp liftNat_injective)).trans (MulEquiv.subgroupCongr s.range_liftNat)

theorem psiNat_apply (z : alternatingGroup (Fin n)) :
    ((s.psiNat z : A) : G) = Φ (liftNat n z) :=
  rfl

theorem rootLast_mem_centralizer : Φ (rootLast n) ∈ centralizer (A : Set G) := by
  rw [mem_centralizer_iff]
  intro a ha
  obtain ⟨z, rfl⟩ := s.exists_liftNat_eq ha
  rw [← map_mul, ← map_mul, commute_rootLast_liftNat]

theorem map_rootLast_ne_one : Φ (rootLast n) ≠ 1 := fun h =>
  rootLast_ne_one (s.injective (h.trans (map_one Φ).symm))

theorem odd_card_centralizer : Odd (Nat.card (centralizer (Φ.range : Set G))) := by
  have hc := s.sec3
  have hKt := RankTwoSporadic.tightlyEmbedded_centralizer_of_standard hc.hyp.standard
  have h := hKt.2 g (by rw [normalizer_centralizer_eq hc.hyp.standard]; exact hc.not_mem)
  rw [← AS76b.centralizer_rightConjugate] at h
  have hle : centralizer (Φ.range : Set G) ≤
      centralizer (A : Set G) ⊓ centralizer (rightConjugate A g : Set G) :=
    le_inf (centralizer_le s.le_range) (centralizer_le s.le_range')
  exact Odd.of_dvd_nat h (Subgroup.card_dvd_of_le hle)

open scoped Pointwise in
theorem mem_of_mem_sup_of_mul_self {w : G} (hw : w ∈ Φ.range ⊔ centralizer (Φ.range : Set G))
    (h2 : w * w = 1) : w ∈ Φ.range := by
  have hle : centralizer (Φ.range : Set G) ≤ normalizer (Φ.range : Set G) :=
    centralizer_le_normalizer _
  have hw' : w ∈ ((Φ.range : Set G) * (centralizer (Φ.range : Set G) : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hle]
    exact hw
  obtain ⟨y, hy, c, hc, rfl⟩ := Set.mem_mul.mp hw'
  have hyc : y * c = c * y := mem_centralizer_iff.mp hc y hy
  have hy2 : y * y * (c * c) = 1 := by
    calc y * y * (c * c) = y * (y * c) * c := by group
      _ = y * (c * y) * c := by rw [hyc]
      _ = y * c * (y * c) := by group
      _ = 1 := h2
  have hyy : y * y ∈ centralizer (Φ.range : Set G) := by
    have : y * y = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left hy2
    rw [this]
    exact inv_mem (mul_mem hc hc)
  obtain ⟨π, rfl⟩ := hy
  have hπ : π * π = 1 := by
    have h1 : ∀ β : alternatingGroup (Fin (n + 4)), (π * π) * β = β * (π * π) := by
      intro β
      apply s.injective
      rw [map_mul, map_mul, map_mul, map_mul]
      exact (mem_centralizer_iff.mp hyy (Φ β) ⟨β, rfl⟩).symm
    have h2 : ((π * π : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = 1 := by
      refine
        LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
          (by simp only [Fintype.card_fin]; have := s.five_le; omega) fun β hβ => ?_
      have := congrArg Subtype.val (h1 ⟨β, hβ⟩)
      exact this
    exact Subtype.ext h2
  have hcc : c * c = 1 := by
    rw [← map_mul, hπ, map_one, one_mul] at hy2
    exact hy2
  have hc1 : c = 1 := by
    have hodd : Odd (orderOf c) :=
      s.odd_card_centralizer.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hc)
    have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hcc])
    have h1 : orderOf c = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h1
  rw [hc1, mul_one]
  exact ⟨π, rfl⟩

theorem centralizer_le_normalizer :
    centralizer (A : Set G) ≤ normalizer (Φ.range : Set G) := by
  intro k hk
  have hkA : k ∈ normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hk
  have hkB : k ∈ normalizer (rightConjugate A g : Set G) :=
    NormPair.centralizer_le_normalizer_B s.sec3 s.T_le hk
  apply mem_normalizer_of_conj_mem
  rw [s.range_eq]
  intro t ht
  have hle : A ⊔ rightConjugate A g ≤
      (A ⊔ rightConjugate A g).comap (MulAut.conj k).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact mem_sup_left ((mem_normalizer_iff.mp hkA a).mp ha)
    · exact mem_sup_right ((mem_normalizer_iff.mp hkB b).mp hb)
  exact hle ht

theorem sign_actPermY {k : G} (hk : k ∈ centralizer (A : Set G)) :
    sign (actPermY (by have := s.five_le; omega) s.injective
      ⟨k, s.centralizer_le_normalizer hk⟩) = 1 := by
  have h5 := s.five_le
  set hkN := s.centralizer_le_normalizer hk
  set κ := actPermY (by omega : 7 ≤ n + 4) s.injective
  obtain ⟨e, b, hb, hkb⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; exact absurd hb (by decide)
  have hord : orderOf (k ^ b) = 2 ^ e := by
    rw [orderOf_pow_of_dvd hb0 (by rw [hkb]; exact dvd_mul_left _ _), hkb,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)]
  obtain ⟨c, hcK, hcR⟩ := exists_conj_mem_of_isSylowOf_two s.sec3.sylowR
    (pow_mem hk b) hord
  have hcN := s.centralizer_le_normalizer hcK
  obtain ⟨π, hπ⟩ := s.le_range' (s.R_le hcR)
  have h1 : (⟨c, hcN⟩ : normalizer (Φ.range : Set G)) * ⟨k, hkN⟩ ^ b * ⟨c, hcN⟩⁻¹ =
      ⟨Φ π, le_normalizer ⟨π, rfl⟩⟩ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow]
    exact hπ.symm)
  have h2 := congrArg (fun x => sign (κ x)) h1
  simp only [map_mul, map_inv, map_pow] at h2
  rw [actPermY_phi, show sign (π : Perm (Fin (n + 4))) = 1 from π.2] at h2
  have h3 : sign (κ ⟨k, hkN⟩) ^ b = 1 := by
    have := h2
    rw [mul_comm (sign (κ ⟨c, hcN⟩)), mul_assoc, mul_inv_cancel, mul_one] at this
    exact this
  rcases Int.units_eq_one_or (sign (κ ⟨k, hkN⟩)) with h | h
  · exact h
  · rw [h, hb.neg_one_pow] at h3
    exact absurd h3 (by decide)

theorem centralizer_le :
    centralizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G) := fun _ hk =>
  mem_sup_of_sign (by have := s.five_le; omega) s.injective (s.centralizer_le_normalizer hk)
    (s.sign_actPermY hk)

theorem mem_sup_of_conjPerm_liftNat {x : G} (σ : Perm (Fin n))
    (hact : ∀ z : alternatingGroup (Fin n),
      Φ (liftNat n (conjPerm n σ z)) = x * Φ (liftNat n z) * x⁻¹) :
    x ∈ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  set ε : Perm (Fin 4) := if sign σ = 1 then 1 else swap 0 1 with hε
  set πP : Perm (Fin (n + 4)) :=
    viaEmbeddingHom (Fin.castLEEmb (by omega : n ≤ n + 4)) σ *
      viaEmbeddingHom (Fin.natAddEmb n) ε with hπP
  have hsign : sign πP = 1 := by
    rw [hπP, Perm.sign_mul, sign_viaEmbeddingHom, sign_viaEmbeddingHom, hε]
    rcases Int.units_eq_one_or (sign σ) with h | h <;> simp [h, sign_swap']
  set π : alternatingGroup (Fin (n + 4)) := ⟨πP, hsign⟩
  have hconj : ∀ z : alternatingGroup (Fin n),
      π * liftNat n z * π⁻¹ = liftNat n (conjPerm n σ z) := by
    intro z
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_liftNat, conjPerm_apply]
    set C := viaEmbeddingHom (Fin.castLEEmb (by omega : n ≤ n + 4))
    set D := viaEmbeddingHom (Fin.natAddEmb n) ε
    have hcomm : C (z : Perm (Fin n)) * D = D * C (z : Perm (Fin n)) := commute_castLE_natAdd _ _
    show C σ * D * C (z : Perm (Fin n)) * (C σ * D)⁻¹ = C (σ * (z : Perm (Fin n)) * σ⁻¹)
    calc C σ * D * C (z : Perm (Fin n)) * (C σ * D)⁻¹ =
        C σ * (D * C (z : Perm (Fin n))) * D⁻¹ * (C σ)⁻¹ := by group
      _ = C σ * C (z : Perm (Fin n)) * (C σ)⁻¹ := by rw [← hcomm]; group
      _ = C (σ * (z : Perm (Fin n)) * σ⁻¹) := by simp only [map_mul, map_inv]
  have hK : (Φ π)⁻¹ * x ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨z, rfl⟩ := s.exists_liftNat_eq ha
    have h1 := hact z
    rw [← hconj z, map_mul, map_mul, map_inv] at h1
    calc Φ (liftNat n z) * ((Φ π)⁻¹ * x) =
        (Φ π)⁻¹ * (Φ π * Φ (liftNat n z) * (Φ π)⁻¹) * x := by group
      _ = (Φ π)⁻¹ * (x * Φ (liftNat n z) * x⁻¹) * x := by rw [h1]
      _ = (Φ π)⁻¹ * x * Φ (liftNat n z) := by group
  have h := mul_mem (mem_sup_left (⟨π, rfl⟩ : Φ π ∈ Φ.range) :
    Φ π ∈ Φ.range ⊔ centralizer (Φ.range : Set G)) (s.centralizer_le hK)
  rwa [mul_inv_cancel_left] at h

theorem normalizer_le_of (hn : n = 5 ∨ 7 ≤ n) :
    normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  intro x hx
  obtain ⟨σ, hσ⟩ := conjPerm_surjective hn
    ((MulAut.congr s.psiNat.symm) (Lemma39.normConj A ⟨x, hx⟩))
  refine s.mem_sup_of_conjPerm_liftNat σ fun z => ?_
  rw [hσ, MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← psiNat_apply s, MulEquiv.apply_symm_apply, Lemma39.normConj_apply, psiNat_apply]

theorem centralizer_rootLast_le_of
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G)) :
    centralizer ({Φ (rootLast n)} : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  have h := Lemma39.centralizer_le_normalizer_rightConjugate s.sec3.hyp 1 (t := Φ (rootLast n))
    (by rw [rightConjugate_one]; exact s.rootLast_mem_centralizer) s.map_rootLast_ne_one
    (by rw [sq]; exact map_rootLast_mul_self Φ)
  rw [rightConjugate_one] at h
  exact h.trans hN

end AltGenCore

namespace AltGenSetting

variable {A R T : Subgroup G} {g : G} {n : ℕ} {Φ : alternatingGroup (Fin (n + 4)) →* G}
  (s : AltGenSetting A R T g n Φ)
include s

theorem exists_liftA_eq {a : G} (ha : a ∈ A) : ∃ z, Φ (liftA s.six_le z) = a := by
  rw [← s.range_liftA] at ha
  exact ha

theorem liftA_mem (z : alternatingGroup (Fin n)) : Φ (liftA s.six_le z) ∈ A := by
  have h : Φ (liftA s.six_le z) ∈ (Φ.comp (liftA s.six_le)).range := ⟨z, rfl⟩
  rwa [s.range_liftA] at h

@[expose] noncomputable def psiA : alternatingGroup (Fin n) ≃* A :=
  (MonoidHom.ofInjective (f := Φ.comp (liftA s.six_le))
    (s.injective.comp (liftA_injective s.six_le))).trans (MulEquiv.subgroupCongr s.range_liftA)

theorem psiA_apply (z : alternatingGroup (Fin n)) :
    ((s.psiA z : A) : G) = Φ (liftA s.six_le z) :=
  rfl

theorem mem_sup_of_conjPerm {x : G} (σ : Perm (Fin n))
    (hact : ∀ z : alternatingGroup (Fin n),
      Φ (liftA s.six_le (conjPerm n σ z)) = x * Φ (liftA s.six_le z) * x⁻¹) :
    x ∈ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  have hn := s.six_le
  set ε : Perm (Fin 4) := if sign σ = 1 then 1 else swap 0 1 with hε
  set πP : Perm (Fin (n + 4)) :=
    viaEmbeddingHom (Fin.castLEEmb (by omega : n ≤ n + 4)) (tau45 hn * σ * (tau45 hn)⁻¹) *
      viaEmbeddingHom (Fin.natAddEmb n) ε with hπP
  have hsign : sign πP = 1 := by
    rw [hπP, Perm.sign_mul, sign_viaEmbeddingHom, sign_viaEmbeddingHom, Perm.sign_mul,
      Perm.sign_mul, Perm.sign_inv, hε]
    rcases Int.units_eq_one_or (sign σ) with h | h <;> simp [h, sign_swap']
  set π : alternatingGroup (Fin (n + 4)) := ⟨πP, hsign⟩
  have hconj : ∀ z : alternatingGroup (Fin n),
      π * liftA hn z * π⁻¹ = liftA hn (conjPerm n σ z) := by
    intro z
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_liftA, conjPerm_apply]
    set C := viaEmbeddingHom (Fin.castLEEmb (by omega : n ≤ n + 4))
    set D := viaEmbeddingHom (Fin.natAddEmb n) ε
    have hcomm : C (tau45 hn * (z : Perm (Fin n)) * (tau45 hn)⁻¹) * D =
        D * C (tau45 hn * (z : Perm (Fin n)) * (tau45 hn)⁻¹) := commute_castLE_natAdd _ _
    show C (tau45 hn * σ * (tau45 hn)⁻¹) * D * C (tau45 hn * (z : Perm (Fin n)) * (tau45 hn)⁻¹) *
        (C (tau45 hn * σ * (tau45 hn)⁻¹) * D)⁻¹ =
      C (tau45 hn * (σ * (z : Perm (Fin n)) * σ⁻¹) * (tau45 hn)⁻¹)
    calc C (tau45 hn * σ * (tau45 hn)⁻¹) * D * C (tau45 hn * (z : Perm (Fin n)) * (tau45 hn)⁻¹) *
          (C (tau45 hn * σ * (tau45 hn)⁻¹) * D)⁻¹ =
        C (tau45 hn * σ * (tau45 hn)⁻¹) * (D * C (tau45 hn * (z : Perm (Fin n)) * (tau45 hn)⁻¹)) *
          D⁻¹ * (C (tau45 hn * σ * (tau45 hn)⁻¹))⁻¹ := by group
      _ = C (tau45 hn * σ * (tau45 hn)⁻¹) * C (tau45 hn * (z : Perm (Fin n)) * (tau45 hn)⁻¹) *
          (C (tau45 hn * σ * (tau45 hn)⁻¹))⁻¹ := by rw [← hcomm]; group
      _ = C (tau45 hn * σ * (tau45 hn)⁻¹ * (tau45 hn * (z : Perm (Fin n)) * (tau45 hn)⁻¹) *
          (tau45 hn * σ * (tau45 hn)⁻¹)⁻¹) := by simp only [map_mul, map_inv]
      _ = C (tau45 hn * (σ * (z : Perm (Fin n)) * σ⁻¹) * (tau45 hn)⁻¹) := by congr 1; group
  have hK : (Φ π)⁻¹ * x ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨z, rfl⟩ := s.exists_liftA_eq ha
    have h1 := hact z
    rw [← hconj z, map_mul, map_mul, map_inv] at h1
    calc Φ (liftA hn z) * ((Φ π)⁻¹ * x) =
        (Φ π)⁻¹ * (Φ π * Φ (liftA hn z) * (Φ π)⁻¹) * x := by group
      _ = (Φ π)⁻¹ * (x * Φ (liftA hn z) * x⁻¹) * x := by rw [h1]
      _ = (Φ π)⁻¹ * x * Φ (liftA hn z) := by group
  have h := mul_mem (mem_sup_left (⟨π, rfl⟩ : Φ π ∈ Φ.range) :
    Φ π ∈ Φ.range ⊔ centralizer (Φ.range : Set G)) (s.centralizer_le hK)
  rwa [mul_inv_cancel_left] at h

theorem normalizer_le (h7 : 7 ≤ n) :
    normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  intro x hx
  have hn := s.six_le
  obtain ⟨σ, hσ⟩ := conjPerm_surjective (Or.inr h7)
    ((MulAut.congr s.psiA.symm) (Lemma39.normConj A ⟨x, hx⟩))
  refine s.mem_sup_of_conjPerm σ fun z => ?_
  rw [hσ, MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← psiA_apply s, MulEquiv.apply_symm_apply, Lemma39.normConj_apply, psiA_apply]

end AltGenSetting

end CFSG.ComponentClassification.RankTwoAlt
