module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BTests
public import CFSG.Sporadic.Co1Block.TwoBComp
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1PW

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open Subgroup CFSG.Open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Monster.B.Co2
  CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

section Generic

variable {C : Type*} [Group C]

theorem commutator_le_self' (L : Subgroup C) : ⁅L, L⁆ ≤ L :=
  commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem commutatorElement_mul_right_of_comm {x y k : C} (h : x * k = k * x) :
    ⁅x, y * k⁆ = ⁅x, y⁆ := by
  simp only [commutatorElement_def, mul_inv_rev]
  have h' : k * x⁻¹ = x⁻¹ * k := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
  calc x * (y * k) * x⁻¹ * (k⁻¹ * y⁻¹) = x * y * (k * x⁻¹) * k⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * k) * k⁻¹ * y⁻¹ := by rw [h']
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_left_of_comm {x y k : C} (h : k * y = y * k) :
    ⁅x * k, y⁆ = ⁅x, y⁆ := by
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * k * y * (k⁻¹ * x⁻¹) * y⁻¹ = x * (k * y) * k⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * k) * k⁻¹ * x⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutator_le_of_central {H N K : Subgroup C} (hNH : N ≤ H)
    (hK : ∀ k ∈ K, ∀ h ∈ H, k * h = h * k) (hH : ∀ h ∈ H, ∃ l ∈ N, ∃ k ∈ K, h = l * k) :
    ⁅H, H⁆ ≤ ⁅N, N⁆ := by
  rw [commutator_le]
  intro h₁ h₁H h₂ h₂H
  obtain ⟨l₁, hl₁, k₁, hk₁, rfl⟩ := hH h₁ h₁H
  obtain ⟨l₂, hl₂, k₂, hk₂, rfl⟩ := hH h₂ h₂H
  rw [commutatorElement_mul_right_of_comm (hK k₂ hk₂ _ h₁H).symm,
    commutatorElement_mul_left_of_comm (hK k₁ hk₁ l₂ (hNH hl₂))]
  exact commutator_mem_commutator hl₁ hl₂

variable {n : ℕ} (φ : C →* Equiv.Perm (Fin n))

theorem mem_ker_of_comm {D : Subgroup (Equiv.Perm (Fin n))}
    (hCD : ∀ σ : Equiv.Perm (Fin n), (∀ d ∈ D, σ * d = d * σ) → σ = 1) {L : Subgroup C}
    (hL : L.map φ = D) {b : C} (hb : ∀ l ∈ L, b * l = l * b) : b ∈ φ.ker := by
  refine hCD _ fun d hd => ?_
  rw [← hL] at hd
  obtain ⟨l, hl, rfl⟩ := hd
  rw [← map_mul, ← map_mul, hb l hl]

theorem le_closure_conj_of_simple {D : Subgroup (Equiv.Perm (Fin n))} (hD : IsSimpleGroup D)
    {L : Subgroup C} (hLperf : ⁅L, L⁆ = L) (hLD : L.map φ = D)
    (hker : ∀ k ∈ L, φ k = 1 → ∀ l ∈ L, k * l = l * k) {z : C} (hz : z ∈ L)
    (hz2 : φ (z ^ 2) ≠ 1) : L ≤ closure {y | ∃ p ∈ L, y = p * z ^ 2 * p⁻¹} := by
  set N := closure {y | ∃ p ∈ L, y = p * z ^ 2 * p⁻¹}
  have hNL : N ≤ L := (closure_le _).mpr fun y ⟨p, hp, hy⟩ => by
    rw [hy]
    exact mul_mem (mul_mem hp (pow_mem hz 2)) (inv_mem hp)
  have hNn : ∀ l ∈ L, ∀ m ∈ N, l * m * l⁻¹ ∈ N := by
    intro l hl m hm
    have hle : N ≤ N.comap (MulAut.conj l).toMonoidHom := (closure_le _).mpr
      fun y ⟨p, hp, hy⟩ => by
        rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hy]
        exact subset_closure ⟨l * p, mul_mem hl hp, by group⟩
    exact hle hm
  let M : Subgroup D := (N.map φ).subgroupOf D
  have hND : N.map φ ≤ D := hLD ▸ map_mono hNL
  have hMn : M.Normal := ⟨fun m hm d => by
    rw [mem_subgroupOf] at hm ⊢
    obtain ⟨y, hy, hye⟩ := hm
    have hd : (d : Equiv.Perm (Fin n)) ∈ L.map φ := hLD ▸ d.2
    obtain ⟨l, hl, hle⟩ := hd
    refine ⟨l * y * l⁻¹, hNn l hl y hy, ?_⟩
    simp only [coe_mul, map_mul, map_inv, hye, hle, coe_inv]⟩
  have hMtop : M = ⊤ := by
    rcases hMn.eq_bot_or_eq_top with h | h
    · exfalso
      apply hz2
      have hmem : φ (z ^ 2) ∈ N.map φ :=
        ⟨z ^ 2, subset_closure ⟨1, one_mem _, by group⟩, rfl⟩
      have hmemD : (⟨φ (z ^ 2), hND hmem⟩ : D) ∈ M := hmem
      rw [h, mem_bot] at hmemD
      exact congrArg Subtype.val hmemD
    · exact h
  have hdec : ∀ l ∈ L, ∃ m ∈ N, ∃ k ∈ L ⊓ φ.ker, l = m * k := by
    intro l hl
    have hlD : φ l ∈ D := hLD ▸ ⟨l, hl, rfl⟩
    have : (⟨φ l, hlD⟩ : D) ∈ M := hMtop ▸ mem_top _
    obtain ⟨m, hm, hme⟩ := this
    have hme' : φ m = φ l := hme
    refine ⟨m, hm, m⁻¹ * l, mem_inf.mpr ⟨mul_mem (inv_mem (hNL hm)) hl, ?_⟩, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hme', inv_mul_cancel]
  have hK : ∀ k ∈ L ⊓ φ.ker, ∀ l ∈ L, k * l = l * k := fun k hk l hl =>
    hker k (mem_inf.mp hk).1 (MonoidHom.mem_ker.mp (mem_inf.mp hk).2) l hl
  calc L = ⁅L, L⁆ := hLperf.symm
    _ ≤ ⁅N, N⁆ := commutator_le_of_central hNL hK hdec
    _ ≤ N := commutator_le_self' N

theorem commutator_eq_self_of_simple {D : Subgroup C} (hD : IsSimpleGroup D) {a b : C}
    (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ≠ b * a) : ⁅D, D⁆ = D := by
  rw [← Subgroup.map_subtype_commutator]
  have htop : commutator D = ⊤ := by
    rcases (commutator_normal (⊤ : Subgroup D) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      apply hab
      have hc : ⁅(⟨a, ha⟩ : D), ⟨b, hb⟩⁆ ∈ commutator D :=
        commutator_mem_commutator (mem_top _) (mem_top _)
      rw [show commutator D = ⁅(⊤ : Subgroup D), ⊤⁆ from rfl, h, mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at hc
      exact congrArg Subtype.val hc
    · exact h
  rw [htop, ← MonoidHom.range_eq_map, range_subtype]

theorem mem_of_card_le {K : Subgroup C} [Finite K] {S : Set C} (hSf : S.Finite) (hSK : S ⊆ K)
    (hK : Nat.card K ≤ S.ncard) {k : C} (hk : k ∈ K) : k ∈ S := by
  by_contra hkS
  have hsub : insert k S ⊆ (K : Set C) := Set.insert_subset hk hSK
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem hkS hSf] at h1
  have h2 : (K : Set C).ncard = Nat.card K := (Nat.card_coe_set_eq _).symm
  omega

@[expose] def fourSet (a b : C) : Set C := {1, a, b, a * b}

theorem ncard_four {a b : C} (ha : a ≠ 1) (hb : b ≠ 1) (hab : b ≠ a) (ha2 : a * a = 1) :
    (fourSet a b).ncard = 4 := by
  unfold fourSet
  have h1 : a * b ≠ 1 := fun h => hab (by
    calc b = a * a * b := by rw [ha2, one_mul]
      _ = a * (a * b) := mul_assoc _ _ _
      _ = a := by rw [h, mul_one])
  have h2 : a * b ≠ a := fun h => hb (by
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have h3 : a * b ≠ b := fun h => ha (by
    calc a = a * b * b⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  rw [Set.ncard_insert_of_notMem (by simp [ha.symm, hb.symm, h1.symm]),
    Set.ncard_insert_of_notMem (by simp [hab.symm, h2.symm]),
    Set.ncard_pair h3.symm]

theorem comm_of_mem_closure' {s : Set C} {g x : C} (hs : ∀ y ∈ s, g * y = y * g)
    (hx : x ∈ Subgroup.closure s) : g * x = x * g := by
  have hle : Subgroup.closure s ≤ Subgroup.centralizer {g} :=
    (Subgroup.closure_le _).mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hs y hy).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm

theorem comm_of_mem_inf_centralizer {H : Subgroup C} {g x : C}
    (hx : x ∈ H ⊓ Subgroup.centralizer ({g} : Set C)) : x * g = g * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2

theorem mul_mem_ker' {P : Type*} [Group P] {φ : C →* P} {a b : C} (ha : φ a = 1)
    (hb : φ b = 1) : a * b ∈ φ.ker := by
  rw [MonoidHom.mem_ker, map_mul, ha, hb, one_mul]

theorem subset_ker_of {P : Type*} [Group P] {φ : C →* P} {a b : C} (ha : φ a = 1)
    (hb : φ b = 1) : fourSet a b ⊆ φ.ker := by
  intro x hx
  unfold fourSet at hx
  rcases hx with h | h | h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact ha
  · rw [h]; exact hb
  · rw [Set.mem_singleton_iff.mp h]; exact mul_mem_ker' ha hb

theorem mem_four {a b x : C} (hx : x ∈ fourSet a b) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  unfold fourSet at hx
  rcases hx with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Set.mem_singleton_iff.mp h)))

theorem comm_of_mem_closure_pair {s t g x : C} (hs : g * s = s * g) (ht : g * t = t * g)
    (hx : x ∈ Subgroup.closure ({s, t} : Set C)) : g * x = x * g := by
  refine comm_of_mem_closure' (fun y hy => ?_) hx
  rcases Set.mem_insert_iff.mp hy with h | h
  · rw [h]; exact hs
  · rw [Set.mem_singleton_iff.mp h]; exact ht

end Generic

section Cent


theorem exists_moved (hm : co1Cen2BMovedOK twoBHSteps = true) (j : Fin 3) :
    ∃ g ∈ twoBH, g (twoBXs j) ≠ twoBXs j := by
  simp only [co1Cen2BMovedOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Array.any_eq_true, bne_iff_ne, ne_eq] at hm
  have key : ∀ p : ℕ, (hp : p < 1365) → (∃ i, ∃ hi : i < twoBHSteps.size, ¬ twoBHSteps[i][p]! = p) →
      ∃ g ∈ twoBH, g ⟨p, hp⟩ ≠ ⟨p, hp⟩ := by
    rintro p hp ⟨i, hi, hne⟩
    refine ⟨twoBHGens.getD i 1, ?_, fun h => hne ?_⟩
    · rw [twoBHGens_getD hi]
      refine subset_closure ?_
      show permOfArr 1365 twoBHSteps[i]! ∈ twoBHGens
      simp only [twoBHGens, List.mem_map, Array.mem_toList_iff]
      exact ⟨twoBHSteps[i]!, by rw [getElem!_pos twoBHSteps i hi]; exact Array.getElem_mem hi, rfl⟩
    · rw [twoBHGens_getD hi] at h
      have hrep := (twoBHSteps_rep hi).apply hp
      rw [h] at hrep
      rw [getElem!_pos twoBHSteps i hi] at hrep
      exact hrep
  obtain ⟨h1, h5, h83⟩ := hm
  have e : ∀ (j : Fin 3) (p : ℕ) (hp : p < 1365), twoBSubReps[(j : ℕ)]! = p →
      twoBXs j = ⟨p, hp⟩ := by
    intro j p hp hjp
    show finPt 1365 twoBSubReps[(j : ℕ)]! = _
    rw [hjp, finPt_eq hp]
  match j with
  | ⟨0, h0⟩ =>
    rw [e ⟨0, h0⟩ 1 (by norm_num) rfl]
    exact key 1 (by norm_num) (by simpa using h1)
  | ⟨1, h1'⟩ =>
    rw [e ⟨1, h1'⟩ 5 (by norm_num) rfl]
    exact key 5 (by norm_num) (by simpa using h5)
  | ⟨2, h2⟩ =>
    rw [e ⟨2, h2⟩ 83 (by norm_num) rfl]
    exact key 83 (by norm_num) (by simpa using h83)

theorem eq_one_of_comm_twoBD (hm : co1Cen2BMovedOK twoBHSteps = true)
    (σ : Equiv.Perm (Fin 1365)) (hσ : ∀ d ∈ twoBD, σ * d = d * σ) : σ = 1 := by
  have hfix : ∀ h ∈ twoBH, h (σ 0) = σ 0 := by
    intro h hh
    have e := congrArg (fun τ : Equiv.Perm (Fin 1365) => τ 0) (hσ h (twoBH_le hh))
    simp only [Equiv.Perm.mul_apply, twoBH_fix h hh] at e
    exact e.symm
  have h0 : σ 0 = 0 := by
    by_contra hne
    obtain ⟨j, h, hh, hhp⟩ := twoB_cover (σ 0) hne
    obtain ⟨g, hg, hgm⟩ := exists_moved hm j
    apply hgm
    have hc := hfix (h * g * h⁻¹) (mul_mem (mul_mem hh hg) (inv_mem hh))
    rw [← hhp] at hc
    have e1 : (h * g * h⁻¹) (h (twoBXs j)) = h (g (twoBXs j)) := by
      simp [Equiv.Perm.mul_apply]
    rw [e1] at hc
    exact h.injective hc
  ext q
  obtain ⟨⟨d, hd⟩, hdq⟩ := MulAction.exists_smul_eq twoBD (0 : Fin 1365) q
  have hdq' : d 0 = q := hdq
  have e := congrArg (fun τ : Equiv.Perm (Fin 1365) => τ 0) (hσ d hd)
  simp only [Equiv.Perm.mul_apply, h0, hdq'] at e
  rw [Equiv.Perm.one_apply, e]

end Cent

noncomputable irreducible_def co1XC :
    C₁ := d₂C twoBXY.1

noncomputable irreducible_def co1YC :
    C₁ := d₂C twoBXY.2

noncomputable irreducible_def co1E2C :
    C₁ := (co1XC * co1YC) ^ 13

noncomputable irreducible_def co1A1C : C₁ :=
  ⟨a₁, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

noncomputable irreducible_def co1E2G :
    GL24 := ((co1E2C : GA) : GL24)

section Concrete


@[expose] noncomputable def co1RSet : Set GL24 := {1, A₁, co1E2G, A₁ * co1E2G}

noncomputable abbrev co1HC : Subgroup C₁ := Subgroup.closure {co1XC, co1YC}

noncomputable abbrev co1LC : Subgroup C₁ := ⁅co1HC, co1HC⁆

theorem triHom_co1XC : triHom co1XC = xBar := by
  rw [co1XC_def]

theorem triHom_co1YC : triHom co1YC = yBar := by
  rw [co1YC_def]

theorem map_co1HC : co1HC.map triHom = twoBD := by
  rw [MonoidHom.map_closure, Set.image_pair, triHom_co1XC, triHom_co1YC]

theorem map_co1LC : co1LC.map triHom = twoBD := by
  rw [map_commutator, map_co1HC]
  exact commutator_eq_self_of_simple isSimpleGroup_twoBD xBar_mem yBar_mem
    (fun h => xD_yD_ne (Subtype.ext h))

theorem eq_of_coe {c d : C₁} (h : ((c : GA) : GL24) = ((d : GA) : GL24)) : c = d :=
  Subtype.ext (Subtype.ext h)

theorem coe_mul_C (c d : C₁) :
    ((c * d : C₁) : GA) = ((c : GA) : GL24) * ((d : GA) : GL24) := rfl

theorem coe_one_C : (((1 : C₁) : GA) : GL24) = 1 := rfl

theorem coe_pow_C (c : C₁) (n : ℕ) : (((c ^ n : C₁) : GA) : GL24) = ((c : GA) : GL24) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, coe_mul_C, ih, pow_succ]

theorem comm_of_coe {c d : C₁}
    (h : ((c : GA) : GL24) * ((d : GA) : GL24) = ((d : GA) : GL24) * ((c : GA) : GL24)) :
    c * d = d * c :=
  eq_of_coe ((coe_mul_C c d).trans (h.trans (coe_mul_C d c).symm))

theorem sq_of_coe {c : C₁} (h : ((c : GA) : GL24) * ((c : GA) : GL24) = 1) : c * c = 1 :=
  eq_of_coe ((coe_mul_C c c).trans (h.trans coe_one_C.symm))

theorem eq_one_of_coe {c : C₁} (h : ((c : GA) : GL24) = 1) : c = 1 :=
  eq_of_coe (h.trans coe_one_C.symm)

theorem ιC_apply (c : C₁) : ιC c = ((c : GA) : GL24) := rfl

theorem rep_co1XC : MRep twoBXYRows.1 ((co1XC : GA) : GL24) := by
  rw [co1XC_def]
  exact rep_d₂C twoBXY.1

theorem rep_co1YC : MRep twoBXYRows.2 ((co1YC : GA) : GL24) := by
  rw [co1YC_def]
  exact rep_d₂C twoBXY.2

theorem co1E2C_eq : co1E2C = (co1XC * co1YC) ^ 13 := co1E2C_def

theorem rep_co1E2C : MRep co1E2R ((co1E2C : GA) : GL24) := by
  rw [co1E2C_eq, coe_pow_C, coe_mul_C]
  exact (rep_co1XC.mul rep_co1YC).pow 13

theorem coe_co1A1C : ((co1A1C : GA) : GL24) = A₁ := by
  rw [co1A1C_def]

theorem rep_co1A1C : MRep Native.aR ((co1A1C : GA) : GL24) := by
  rw [coe_co1A1C]
  exact rep_A₁

theorem co1E2G_eq : co1E2G = ((co1E2C : GA) : GL24) := co1E2G_def

theorem comm_co1A1C (h : C₁) : co1A1C * h = h * co1A1C := by
  have hh := comm_of_mem_inf_centralizer (coe_mem_C₁ h)
  exact comm_of_coe (by rw [coe_co1A1C]; exact hh.symm)

structure Cen2BFacts : Prop where
  a1_ne : co1A1C ≠ 1
  e2_ne : co1E2C ≠ 1
  e2_ne_a1 : co1E2C ≠ co1A1C
  a1_sq : co1A1C * co1A1C = 1
  e2_x : co1E2C * co1XC = co1XC * co1E2C
  e2_y : co1E2C * co1YC = co1YC * co1E2C
  phi_a1 : triHom co1A1C = 1
  phi_e2 : triHom co1E2C = 1
  outer : ∃ c : C₁, triHom c ∉ twoBD
  zL : ∃ z ∈ co1LC, z ^ 8 = 1 ∧ triHom (z ^ 2) ≠ 1
  moved : co1Cen2BMovedOK twoBHSteps = true

theorem sift_of_mem_twoBD {g : Array ℕ} {G : Equiv.Perm (Fin 1365)} (hG : Rep 1365 g G)
    (h : G ∈ twoBD) :
    CFSG.Monster.B.Co2.Native.siftA 1365
      (CFSG.Certificates.Native.rawLevels 1365 twoBStrong twoBChainBase.toArray)
      twoBChainBase.toArray 0 g = true := by
  rw [← twoBQ_original] at h
  have := (siftA_iff_mem_ofArrays twoB_allPerms (by norm_num : 0 < 4) twoB_chainOK hG).2 h
  rwa [twoB_baseArr] at this

theorem rows_eq_of_mrep {X Y : Native.Rows} {g : GL24}
    (hX : CFSG.Sporadic.Co1.InvNative.validRows X = true)
    (hY : CFSG.Sporadic.Co1.InvNative.validRows Y = true) (hXg : MRep X g) (hYg : MRep Y g) :
    X = Y :=
  CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hX hY (hXg.trans hYg.symm)

theorem cen2BFacts_of_check {hd : List (List ℕ)} {uv : ℕ × ℕ} {cd : List (List ℕ)} {ic : ℕ}
    (h : co1Cen2BCheck hd uv cd ic = true) : Cen2BFacts := by
  simp only [co1Cen2BCheck, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, and_assoc] at h
  obtain ⟨hvE, hvA, hA1, hAsq, hEsq, hE1, hEA, hcEA, hcEx, hcEy, hHD, hinv, hz8, hCD, hc0,
    htri, hmov⟩ := h
  simp only [co1Cen2BTriOK, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at htri
  obtain ⟨htA, hpA, htE, hpE, htZ, hpZ, htC, hsC⟩ := htri
  have hvOne := validRows_one
  have hE := rep_co1E2C
  have hA := rep_co1A1C
  have hrepH := dag_rep (.cons rep_co1XC (.cons rep_co1YC .nil)) (hd.map Native.decWord) hHD
  have hmemH : ∀ g ∈ dagG [((co1XC : GA) : GL24), ((co1YC : GA) : GL24)]
      (hd.map Native.decWord), g ∈ co1HC.map ιC := by
    refine dagG_mem (fun g hg => ?_) _
    rw [MonoidHom.map_closure, Set.image_pair]
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [List.mem_singleton.mp hg]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hu := mrep_entry hrepH uv.1
  have hv := mrep_entry hrepH uv.2
  simp only [invsOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hinv
  have hz := (hu.mul hv).mul ((hu.inv hinv.1).mul (hv.inv hinv.2))
  obtain ⟨uC, huC, huCe⟩ := entryG_mem hmemH uv.1
  obtain ⟨vC, hvC, hvCe⟩ := entryG_mem hmemH uv.2
  rw [ιC_apply] at huCe hvCe
  have hzC : MRep (commRows
      (entryR (Native.dag [twoBXYRows.1, twoBXYRows.2] (hd.map Native.decWord)).1 uv.1)
      (entryR (Native.dag [twoBXYRows.1, twoBXYRows.2] (hd.map Native.decWord)).1 uv.2))
      ((⁅uC, vC⁆ : C₁) : GA) := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, huCe, hvCe]
    simpa [commRows, mul_assoc] using hz
  refine ⟨fun h1 => hA1 (rows_eq_of_mrep hvA hvOne hA (by rw [h1]; exact MRep.one)),
    fun h1 => hE1 (rows_eq_of_mrep hvE hvOne hE (by rw [h1]; exact MRep.one)),
    fun h1 => hEA (rows_eq_of_mrep hvE hvA hE (by rw [h1]; exact hA)),
    sq_of_coe ((hA.mul hA).eq (hAsq ▸ MRep.one)),
    comm_of_coe (by
      simp only [commR, beq_iff_eq] at hcEx
      exact (hE.mul rep_co1XC).eq (by rw [hcEx]; exact rep_co1XC.mul hE)),
    comm_of_coe (by
      simp only [commR, beq_iff_eq] at hcEy
      exact (hE.mul rep_co1YC).eq (by rw [hcEy]; exact rep_co1YC.mul hE)),
    (eqA_iff (rep_triHom hA htA) rep_idA).mp hpA,
    (eqA_iff (rep_triHom hE htE) rep_idA).mp hpE, ?_, ?_, hmov⟩
  ·
    have hrepC := dag_rep (.cons rep_A₁ (.cons rep_A₂ .nil)) (cd.map Native.decWord) hCD
    have hc0G : entryG (dagG [A₁, A₂] (cd.map Native.decWord)) ic ∈ GA := by
      refine entryG_mem (dagG_mem (fun g hg => ?_) _) ic
      rcases List.mem_cons.mp hg with h1 | hg
      · rw [h1]; exact A₁_mem
      · rw [List.mem_singleton.mp hg]; exact A₂_mem
    have hc0r := mrep_entry hrepC ic
    simp only [commR, beq_iff_eq] at hc0
    have hcomm : entryG (dagG [A₁, A₂] (cd.map Native.decWord)) ic * A₁ =
        A₁ * entryG (dagG [A₁, A₂] (cd.map Native.decWord)) ic :=
      (hc0r.mul rep_A₁).eq (by rw [hc0]; exact rep_A₁.mul hc0r)
    have hmemC : entryG (dagG [A₁, A₂] (cd.map Native.decWord)) ic ∈
        GA ⊓ Subgroup.centralizer {A₁} :=
      Subgroup.mem_inf.mpr ⟨hc0G, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    refine ⟨liftC _ hmemC, fun hD => ?_⟩
    have hrep := rep_triHom (c := liftC _ hmemC) hc0r htC
    have := sift_of_mem_twoBD hrep hD
    rw [this] at hsC
    exact Bool.noConfusion hsC
  ·
    refine ⟨⁅uC, vC⁆, commutator_mem_commutator huC hvC,
      eq_one_of_coe ((coe_pow_C _ 8).trans ((hzC.pow 8).eq (hz8 ▸ MRep.one))), fun h1 => ?_⟩
    have hrep := rep_triHom hzC htZ
    have hsq : triHom ⁅uC, vC⁆ * triHom ⁅uC, vC⁆ = 1 :=
      (map_mul triHom _ _).symm.trans ((congrArg triHom (pow_two _).symm).trans h1)
    have := (eqA_iff (rep_compA hrep hrep) rep_idA).mpr hsq
    rw [this] at hpZ
    exact Bool.noConfusion hpZ

noncomputable abbrev co1R4 : Set C₁ := fourSet co1A1C co1E2C

theorem ker_subset (hF : Cen2BFacts) {k : C₁} (hk : k ∈ triHom.ker) : k ∈ co1R4 := by
  obtain ⟨t, ht, ht8⟩ := exists_card_range_ker
  obtain ⟨c, hc⟩ := hF.outer
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [mul_one] at ht
    have heq : twoBD = triHom.range := Subgroup.eq_of_le_of_card_ge twoBD_le_range ht.le
    exact hc (heq ▸ ⟨c, rfl⟩)
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht8
  have hker : Nat.card triHom.ker ≤ 4 := by
    have : 2 ≤ t := by omega
    have h8 : t * Nat.card triHom.ker = 8 := ht8
    nlinarith [Nat.card_pos (α := triHom.ker)]
  have hsub : co1R4 ⊆ triHom.ker := subset_ker_of hF.phi_a1 hF.phi_e2
  have h4 : co1R4.ncard = 4 := ncard_four hF.a1_ne hF.e2_ne hF.e2_ne_a1 hF.a1_sq
  exact mem_of_card_le (Set.toFinite _) hsub (by rw [h4]; exact hker) hk

theorem ker_comm (hF : Cen2BFacts) {k : C₁} (hk : k ∈ triHom.ker) {h : C₁} (hh : h ∈ co1HC) :
    k * h = h * k := by
  have he2 : ∀ g ∈ co1HC, co1E2C * g = g * co1E2C := fun g hg =>
    comm_of_mem_closure_pair (s := co1XC) (t := co1YC) hF.e2_x hF.e2_y hg
  rcases mem_four (ker_subset hF hk) with e | e | e | e <;> rw [e]
  · rw [one_mul, mul_one]
  · exact comm_co1A1C h
  · exact he2 h hh
  · rw [mul_assoc, he2 h hh, ← mul_assoc, comm_co1A1C h, mul_assoc]

theorem perfect_co1LC (hF : Cen2BFacts) : ⁅co1LC, co1LC⁆ = co1LC := by
  refine le_antisymm (commutator_le_self' _) ?_
  refine commutator_le_of_central (K := triHom.ker) (commutator_le_self' _)
    (fun k hk h hh => ker_comm hF hk hh) fun h hh => ?_
  have hD : triHom h ∈ co1LC.map triHom := by
    rw [map_co1LC, ← map_co1HC]
    exact ⟨h, hh, rfl⟩
  obtain ⟨l, hl, hle⟩ := hD
  refine ⟨l, hl, l⁻¹ * h, ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hle, inv_mul_cancel]

theorem perfGen_co1LC (hF : Cen2BFacts) : PerfGen co1LC := by
  obtain ⟨z, hzL, hz8, hz2⟩ := hF.zL
  refine ⟨perfect_co1LC hF, z, hzL, ?_, ?_⟩
  · obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (show z ^ (2 ^ 3) = 1 from hz8))
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  · exact le_closure_conj_of_simple triHom isSimpleGroup_twoBD (perfect_co1LC hF) map_co1LC
      (fun k hk hk1 l hl => ker_comm hF hk1 (commutator_le_self' _ hl)) hzL hz2

theorem mem_co1RSet (hF : Cen2BFacts) {b : GL24} (hb : b ∈ GA ⊓ Subgroup.centralizer {A₁})
    (hc : ∀ l ∈ co1LC, b * ((l : GA) : GL24) = ((l : GA) : GL24) * b) : b ∈ co1RSet := by
  set bC := liftC b hb
  have hbC : ((bC : GA) : GL24) = b := rfl
  have hcomm : ∀ l ∈ co1LC, bC * l = l * bC := fun l hl =>
    comm_of_coe (by rw [hbC]; exact hc l hl)
  have hk : bC ∈ triHom.ker :=
    mem_ker_of_comm triHom (eq_one_of_comm_twoBD hF.moved) map_co1LC hcomm
  rw [← hbC]
  rcases mem_four (ker_subset hF hk) with h | h | h | h <;> rw [h]
  · exact Or.inl coe_one_C
  · exact Or.inr (Or.inl coe_co1A1C)
  · exact Or.inr (Or.inr (Or.inl co1E2G_eq.symm))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [coe_mul_C, coe_co1A1C, co1E2G_eq]
    exact Set.mem_singleton _

theorem co1_pWitness_a₁ {hd : List (List ℕ)} {uv : ℕ × ℕ} {cd : List (List ℕ)} {ic : ℕ}
    (h : co1Cen2BCheck hd uv cd ic = true) {E : Subgroup GL24} (hEG : E ≤ GA)
    (hE : IsElemAbelian 2 E) (hA : A₁ ∈ E) (hER : ¬ (E : Set GL24) ⊆ co1RSet) :
    PWitness GA E := by
  have hF := cen2BFacts_of_check h
  have hA1 : A₁ ≠ 1 := fun h1 => hF.a1_ne (eq_one_of_coe (coe_co1A1C.trans h1))
  have hPX : co1LC.map ιC ≤ GA ⊓ Subgroup.centralizer {A₁} := by
    rintro _ ⟨l, -, rfl⟩
    exact coe_mem_C₁ l
  obtain ⟨b, hbE, hbR⟩ := Set.not_subset.mp hER
  have hbC : b ∈ GA ⊓ Subgroup.centralizer {A₁} :=
    Subgroup.mem_inf.mpr ⟨hEG hbE, Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_isElemAbelian hE hbE hA)⟩
  refine pWitness_of_perfGen hA hA1 hPX ((perfGen_co1LC hF).map ιC) fun hEC => hbR ?_
  refine mem_co1RSet hF hbC fun l hl => ?_
  have := Subgroup.mem_centralizer_iff.mp (hEC hbE) (ιC l) ⟨l, hl, rfl⟩
  exact this.symm

end Concrete

end CFSG.ComponentClassification.RankTwoSporadic.Co1
