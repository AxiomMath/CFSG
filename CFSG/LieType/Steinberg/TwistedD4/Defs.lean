module

public import CFSG.LieType.Chevalley.TwistHolds
public import CFSG.LieType.Chevalley.RootConj
public import CFSG.LieType.Steinberg.Adjoint.CommAll
public import CFSG.LieType.Steinberg.BruhatTwistBasic

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedD4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Universal
open scoped commutatorElement

abbrev d4 : Tag := TwistTag.D4.tag

abbrev rhoPerm : Equiv.Perm (Fin d4.rank) := TwistTag.D4.perm

abbrev rho (γ : Fin d4.rank → ℤ) : Fin d4.rank → ℤ := permLattice rhoPerm γ

abbrev nd (a : ℕ) (h : a < 4 := by decide) : Fin d4.rank := ⟨a, h⟩

abbrev ng (i : ℕ) (h : i < 2 := by decide) : Fin (Tag.rank .G2) := ⟨i, h⟩

theorem rhoPerm_zero : rhoPerm (nd 0) = nd 1 := rfl

theorem rhoPerm_one : rhoPerm (nd 1) = nd 3 := rfl

theorem rhoPerm_two : rhoPerm (nd 2) = nd 2 := rfl

theorem rhoPerm_three : rhoPerm (nd 3) = nd 0 := rfl

theorem rhoPerm_rhoPerm_rhoPerm (a : Fin d4.rank) : rhoPerm (rhoPerm (rhoPerm a)) = a := by
  revert a
  decide

theorem isRoot_rho {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) : IsRoot d4 (rho γ) :=
  hγ.permLattice (TwistTag.cartan_perm .D4)

theorem rho_single (i : Fin d4.rank) : rho (Pi.single i 1) = Pi.single (rhoPerm i) 1 :=
  permLattice_single rhoPerm i

theorem rho_neg_single
    (i : Fin d4.rank) :
    rho (-Pi.single i 1) = -Pi.single (rhoPerm i) 1 :=
  permLattice_neg_single rhoPerm i

theorem rho_rho_rho (v : Fin d4.rank → ℤ) : rho (rho (rho v)) = v := by
  funext j
  change Fin 4 at j
  fin_cases j <;> rfl

@[expose] def orbitMap : Fin d4.rank → Fin (Tag.rank .G2) :=
  (![1, 1, 0, 1] : Fin 4 → Fin 2)

theorem orbitMap_rhoPerm (a : Fin d4.rank) : orbitMap (rhoPerm a) = orbitMap a := by
  revert a
  decide

theorem orbitSum_single (a : Fin d4.rank) :
    orbitSum orbitMap (Pi.single a 1 : Fin d4.rank → ℤ) = Pi.single (orbitMap a) 1 := by
  revert a
  decide

theorem orbitSum_neg_single (a : Fin d4.rank) :
    orbitSum orbitMap (-Pi.single a 1 : Fin d4.rank → ℤ) = -Pi.single (orbitMap a) 1 := by
  revert a
  decide

theorem symmetrizer_d4 (k : Fin d4.rank) : d4.symmetrizer k k = 1 := by
  revert k
  decide

theorem noG2_D4 : NoG2 d4 := fun i => Or.inl (symmetrizer_d4 i)

theorem not_isRoot_nsmul_add_nsmul
    {γ δ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ)
    (hδ : IsRoot d4 δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ) (hsum : ¬IsRoot d4 (γ + δ)) {i j : ℕ}
    (hi : 1 ≤ i) (hj : 1 ≤ j) : ¬IsRoot d4 (i • γ + j • δ) := by
  intro h
  have h2 : ∀ {ε : Fin d4.rank → ℤ}, IsRoot d4 ε → iform ε ε = 2 := fun hε => by
    obtain ⟨k, hk⟩ := iform_self_of_isRoot hε
    rw [hk, symmetrizer_d4, mul_one]
  rcases exponent_pair_cases noG2_D4 hγ hδ hne hne' hi hj h with ⟨rfl, rfl⟩ | ⟨-, -, h4, -⟩ |
    ⟨-, -, -, h4, -⟩
  · exact hsum (by simpa using h)
  · rw [h2 hγ] at h4
    omega
  · rw [h2 hδ] at h4
    omega

variable {K : Type} [Field K]

theorem commute_of_mem_rootGroup
    {γ δ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ)
    (hδ : IsRoot d4 δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ) (hsum : ¬IsRoot d4 (γ + δ))
    {x y : adjointGroup d4 K} (hx : x ∈ rootGroup (rootOperatorFamily d4) K γ)
    (hy : y ∈ rootGroup (rootOperatorFamily d4) K δ) : Commute x y := by
  have hlin : LinIndepPair γ δ := by
    by_contra h
    rcases CFSG.LieType.Steinberg.TagRoots.eq_or_eq_neg_of_not_linIndepPair hγ hδ h with h' | h'
    exacts [hne h', hne' h']
  have hcone : openCone (adjDatum (rootOperatorFamily d4) K).roots γ δ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun ε ⟨hε, m, n, hm, hn, hεe⟩ => ?_
    rw [mem_adjDatum_roots, hεe] at hε
    exact not_isRoot_nsmul_add_nsmul hγ hδ hne hne' hsum hm hn hε
  have key := commutator_mem_openCone_of_linIndepPair hγ hδ hlin hx hy
  rw [hcone] at key
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at key
  exact commutatorElement_eq_one_iff_commute.1 key

theorem commute_xPar
    {γ δ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (hδ : IsRoot d4 δ)
    (hne : γ ≠ δ) (hne' : γ ≠ -δ) (hsum : ¬IsRoot d4 (γ + δ)) (c d : K) :
    Commute (xPar (rootOperatorFamily d4) γ c) (xPar (rootOperatorFamily d4) δ d) :=
  commute_of_mem_rootGroup hγ hδ hne hne' hsum (xPar_mem hγ c) (xPar_mem hδ d)

theorem isRoot_smul_single {s : ℤ} (hs : s = 1 ∨ s = -1) (a : Fin d4.rank) :
    IsRoot d4 (s • Pi.single a 1) := by
  rcases hs with rfl | rfl
  · rw [one_smul]; exact .basis a
  · rw [neg_one_smul]; exact isRoot_neg_single d4 a

theorem not_isRoot_smul_single_add
    {a b : Fin d4.rank} (ha : a ≠ nd 2) (hb : b ≠ nd 2)
    (hab : a ≠ b) {s s' : ℤ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) :
    ¬IsRoot d4 (s • Pi.single a 1 + s' • Pi.single b 1) := by
  rw [← StringData.memDec_iff (Tag.rootCertificate_check d4) (Tag.stringData_check d4)]
  revert a b
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> decide +kernel

theorem commute_xPar_outer
    {a b : Fin d4.rank} (ha : a ≠ nd 2) (hb : b ≠ nd 2)
    (hab : a ≠ b) {s s' : ℤ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (c d : K) :
    Commute (xPar (rootOperatorFamily d4) (s • Pi.single a 1) c)
      (xPar (rootOperatorFamily d4) (s' • Pi.single b 1) d) := by
  refine commute_xPar (isRoot_smul_single hs a) (isRoot_smul_single hs' b) (fun h => ?_)
    (fun h => ?_) (not_isRoot_smul_single_add ha hb hab hs hs') c d <;>
  · have := congrFun h b
    simp only [Pi.smul_apply, Pi.neg_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab),
      smul_eq_mul, mul_zero, mul_one] at this
    rcases hs' with rfl | rfl <;> omega

variable (σ : K →+* K)

theorem twistC_xPar_single
    (i : Fin d4.rank) (c : K) :
    twistC .D4 K σ (xPar (rootOperatorFamily d4) (Pi.single i 1) c) =
      xPar (rootOperatorFamily d4) (Pi.single (rhoPerm i) 1) (σ c) := by
  rw [xPar_simple, xPar_simple, eltElement_simpleRoot, eltElement_simpleRoot]
  exact twistC_xElement .D4 K σ i c

theorem twistC_xPar_neg_single
    (i : Fin d4.rank) (c : K) :
    twistC .D4 K σ (xPar (rootOperatorFamily d4) (-Pi.single i 1) c) =
      xPar (rootOperatorFamily d4) (-Pi.single (rhoPerm i) 1) (σ c) := by
  have e : ∀ (j : Fin d4.rank) (d : K),
      xPar (rootOperatorFamily d4) (-Pi.single j 1) d = yElement j d := fun j d =>
    (xPar_neg_simple j d).trans (Subtype.ext ((rootOperatorFamily d4).eltUnit_neg_simple j d))
  rw [e, e]
  exact twistC_yElement .D4 K σ i c

theorem twistC_xPar_smul_single
    {s : ℤ} (hs : s = 1 ∨ s = -1) (i : Fin d4.rank) (c : K) :
    twistC .D4 K σ (xPar (rootOperatorFamily d4) (s • Pi.single i 1) c) =
      xPar (rootOperatorFamily d4) (s • Pi.single (rhoPerm i) 1) (σ c) := by
  rcases hs with rfl | rfl
  · simp only [one_smul]
    exact twistC_xPar_single σ i c
  · simp only [neg_one_smul]
    exact twistC_xPar_neg_single σ i c

@[expose] def twistedRootSubgroupD4
    (β : Fin (Tag.rank .G2) → ℤ) :
    Subgroup (adjointGroup d4 K) :=
  twistedRootSubgroup {α | IsRoot d4 α} orbitMap (rootGroup (rootOperatorFamily d4) K)
    (twistC .D4 K σ) β

@[expose] def twistedGroup :
    Subgroup (adjointGroup d4 K) :=
  ⨆ β ∈ {β : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 β}, twistedRootSubgroupD4 σ β

@[expose] def twistedRootGroup
    (β : Fin (Tag.rank .G2) → ℤ) : Subgroup (twistedGroup σ) :=
  (twistedRootSubgroupD4 σ β).subgroupOf (twistedGroup σ)

@[expose] def twistedDatum :
    UniversalRootDatum (twistedGroup σ) where
  rank := Tag.rank .G2
  cartan := Tag.cartan .G2
  isFiniteType := isFiniteType_cartan .G2
  divisible := ∅
  rootGroup := twistedRootGroup σ

theorem twistedRootSubgroupD4_le_twistFixed
    (β : Fin (Tag.rank .G2) → ℤ) :
    twistedRootSubgroupD4 σ β ≤ twistFixed .D4 K σ :=
  inf_le_right

theorem twistedGroup_le_twistFixed :
    twistedGroup σ ≤ twistFixed .D4 K σ :=
  iSup₂_le fun β _ => twistedRootSubgroupD4_le_twistFixed σ β

theorem twistedRootSubgroupD4_le_twistedGroup
    {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β) :
    twistedRootSubgroupD4 σ β ≤ twistedGroup σ :=
  le_iSup₂_of_le (f := fun β (_ : β ∈ {β : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 β}) =>
    twistedRootSubgroupD4 σ β) β hβ le_rfl

theorem mem_twistedRootGroup
    {β : Fin (Tag.rank .G2) → ℤ} {x : twistedGroup σ} :
    x ∈ twistedRootGroup σ β ↔ (x : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ β :=
  Subgroup.mem_subgroupOf

theorem twistedDatum_roots
    : (twistedDatum σ).roots = {β | IsRoot .G2 β} :=
  roots_eq_setOf_isRoot (isFiniteType_cartan .G2)

theorem iSup_twistedRootGroup_eq_subgroupOf
    {S : Set (Fin (Tag.rank .G2) → ℤ)}
    (hS : ∀ β ∈ S, IsRoot .G2 β) :
    ⨆ β ∈ S, twistedRootGroup σ β =
      (⨆ β ∈ S, twistedRootSubgroupD4 σ β).subgroupOf (twistedGroup σ) := by
  have hle : ∀ β, (⨆ (_ : β ∈ S), twistedRootSubgroupD4 σ β) ≤ twistedGroup σ := fun β =>
    iSup_le fun hβ => twistedRootSubgroupD4_le_twistedGroup σ (hS β hβ)
  rw [iSup_subgroupOf hle]
  exact iSup_congr fun β => (iSup_subgroupOf fun hβ =>
    twistedRootSubgroupD4_le_twistedGroup σ (hS β hβ)).symm

theorem iSup_twistedDatum_rootGroup :
    ⨆ β ∈ (twistedDatum σ).roots, (twistedDatum σ).rootGroup β = ⊤ := by
  rw [twistedDatum_roots]
  change ⨆ β ∈ {β : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 β}, twistedRootGroup σ β = ⊤
  rw [iSup_twistedRootGroup_eq_subgroupOf σ (S := {β | IsRoot .G2 β}) fun β hβ => hβ]
  exact Subgroup.subgroupOf_self _

theorem mem_twistedRootSubgroupD4_of_mem_iSup
    {β : Fin (Tag.rank .G2) → ℤ}
    {g : adjointGroup d4 K}
    (hg : g ∈ ⨆ α ∈ {α : Fin d4.rank → ℤ | IsRoot d4 α ∧ orbitSum orbitMap α = β},
      rootGroup (rootOperatorFamily d4) K α)
    (hfix : twistC .D4 K σ g = g) : g ∈ twistedRootSubgroupD4 σ β := by
  refine Subgroup.mem_inf.2 ⟨?_, hfix⟩
  refine (iSup₂_le fun α hα => ?_ : (⨆ α ∈ {α : Fin d4.rank → ℤ |
    IsRoot d4 α ∧ orbitSum orbitMap α = β}, rootGroup (rootOperatorFamily d4) K α) ≤ _) hg
  exact le_iSup₂_of_le (f := fun α (_ : α ∈ {α : Fin d4.rank → ℤ | IsRoot d4 α}) =>
    ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • β), rootGroup (rootOperatorFamily d4) K α)
    α hα.1 (le_iSup_of_le ⟨1, one_pos, by rw [one_smul, hα.2]⟩ le_rfl)

theorem xPar_mem_iSup_fibre
    {a : Fin d4.rank} {b : Fin (Tag.rank .G2)} (hab : orbitMap a = b)
    {s : ℤ} (hs : s = 1 ∨ s = -1) (c : K) :
    xPar (rootOperatorFamily d4) (s • Pi.single a 1) c ∈
      ⨆ α ∈ {α : Fin d4.rank → ℤ | IsRoot d4 α ∧ orbitSum orbitMap α = s • Pi.single b 1},
        rootGroup (rootOperatorFamily d4) K α := by
  have hp : orbitSum orbitMap (s • Pi.single a 1 : Fin d4.rank → ℤ) = s • Pi.single b 1 := by
    rcases hs with rfl | rfl
    · rw [one_smul, one_smul, orbitSum_single, hab]
    · rw [neg_one_smul, neg_one_smul, orbitSum_neg_single, hab]
  exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem ⟨isRoot_smul_single hs a, hp⟩
    (xPar_mem (isRoot_smul_single hs a) c))

theorem xPar_two_mem
    {s : ℤ} (hs : s = 1 ∨ s = -1) {c : K} (hc : σ c = c) :
    xPar (rootOperatorFamily d4) (s • Pi.single (nd 2) 1) c ∈
      twistedRootSubgroupD4 σ (s • Pi.single (ng 0) 1) := by
  refine mem_twistedRootSubgroupD4_of_mem_iSup σ
    (xPar_mem_iSup_fibre (a := nd 2) (b := ng 0) (by decide) hs c) ?_
  rw [twistC_xPar_smul_single σ hs, rhoPerm_two, hc]

@[expose] def xOuter
    (s : ℤ) (c d e : K) : adjointGroup d4 K :=
  xPar (rootOperatorFamily d4) (s • Pi.single (nd 0) 1) c *
    xPar (rootOperatorFamily d4) (s • Pi.single (nd 1) 1) d *
      xPar (rootOperatorFamily d4) (s • Pi.single (nd 3) 1) e

theorem twistC_xOuter
    {s : ℤ} (hs : s = 1 ∨ s = -1) (c d e : K) :
    twistC .D4 K σ (xOuter s c d e) = xOuter s (σ e) (σ c) (σ d) := by
  simp only [xOuter, map_mul, twistC_xPar_smul_single σ hs, rhoPerm_zero, rhoPerm_one,
    rhoPerm_three]
  have h03 := commute_xPar_outer (K := K) (a := nd 0) (b := nd 3) (by decide) (by decide)
    (by decide) hs hs (σ e) (σ d)
  have h01 := commute_xPar_outer (K := K) (a := nd 0) (b := nd 1) (by decide) (by decide)
    (by decide) hs hs (σ e) (σ c)
  rw [mul_assoc, ← h03.eq, ← mul_assoc, ← h01.eq]

theorem xOuter_mem
    {s : ℤ} (hs : s = 1 ∨ s = -1) {c : K} (hc : σ (σ (σ c)) = c) :
    xOuter s c (σ c) (σ (σ c)) ∈ twistedRootSubgroupD4 σ (s • Pi.single (ng 1) 1) := by
  refine mem_twistedRootSubgroupD4_of_mem_iSup σ ?_ ?_
  · exact mul_mem (mul_mem (xPar_mem_iSup_fibre (a := nd 0) (b := ng 1) (by decide) hs c)
      (xPar_mem_iSup_fibre (a := nd 1) (b := ng 1) (by decide) hs _))
      (xPar_mem_iSup_fibre (a := nd 3) (b := ng 1) (by decide) hs _)
  · rw [twistC_xOuter σ hs, hc]

variable (K) in
@[expose] def nHatE
    : Fin (Tag.rank .G2) → adjointGroup d4 K :=
  ![Chevalley.weylElement d4 K (nd 2),
    Chevalley.weylElement d4 K (nd 0) * Chevalley.weylElement d4 K (nd 1) *
      Chevalley.weylElement d4 K (nd 3)]

theorem nHatE_zero
    : nHatE K (ng 0) = Chevalley.weylElement d4 K (nd 2) := rfl

theorem nHatE_one :
    nHatE K (ng 1) = Chevalley.weylElement d4 K (nd 0) * Chevalley.weylElement d4 K (nd 1) *
      Chevalley.weylElement d4 K (nd 3) :=
  rfl

theorem weylElement_eq
    (a : Fin d4.rank) :
    Chevalley.weylElement d4 K a = xPar (rootOperatorFamily d4) ((1 : ℤ) • Pi.single a 1) 1 *
      xPar (rootOperatorFamily d4) ((-1 : ℤ) • Pi.single a 1) (-1) *
        xPar (rootOperatorFamily d4) ((1 : ℤ) • Pi.single a 1) 1 := by
  rw [weylElement_eq_xPar (rootOperatorFamily d4) a, CFSG.LieType.Steinberg.weylElement]
  simp

theorem nHatE_zero_eq :
    nHatE K (ng 0) =
    xPar (rootOperatorFamily d4) ((1 : ℤ) • Pi.single (nd 2) 1) 1 *
      xPar (rootOperatorFamily d4) ((-1 : ℤ) • Pi.single (nd 2) 1) (-1) *
        xPar (rootOperatorFamily d4) ((1 : ℤ) • Pi.single (nd 2) 1) 1 :=
  weylElement_eq (nd 2)

theorem mul3_mul_mul3' {G : Type*} [Group G] {a b c a' b' c' : G} (h1 : Commute b a')
    (h2 : Commute c a') (h3 : Commute c b') :
    a * b * c * (a' * b' * c') = a * a' * (b * b') * (c * c') := by
  calc a * b * c * (a' * b' * c') = a * b * (c * a') * b' * c' := by group
    _ = a * (b * a') * c * b' * c' := by rw [h2.eq]; group
    _ = a * a' * b * (c * b') * c' := by rw [h1.eq]; group
    _ = a * a' * (b * b') * (c * c') := by rw [h3.eq]; group

theorem mul_rearrange_three {G : Type*} [Group G] {a b a' b' a'' b'' : G}
    (h1 : Commute b a') (h2 : Commute a a') (h3 : Commute a b') (h4 : Commute b a'')
    (h5 : Commute b' a'') (h6 : Commute a a'') (h7 : Commute a' a'') (h8 : Commute a b'')
    (h9 : Commute a' b'') :
    a * b * a * (a' * b' * a') * (a'' * b'' * a'') =
      a * a' * a'' * (b * b' * b'') * (a * a' * a'') := by
  rw [mul3_mul_mul3' h1 h2 h3, mul3_mul_mul3' (h4.mul_left h5) (h6.mul_left h7)
    (h8.mul_left h9)]

theorem nHatE_one_eq :
    nHatE K (ng 1) = xOuter 1 1 1 1 * xOuter (-1) (-1) (-1) (-1) * xOuter 1 1 1 1 := by
  have p : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have n : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have c01 := fun {s s' : ℤ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (c d : K) =>
    commute_xPar_outer (a := nd 0) (b := nd 1) (by decide) (by decide) (by decide) hs hs' c d
  have c03 := fun {s s' : ℤ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (c d : K) =>
    commute_xPar_outer (a := nd 0) (b := nd 3) (by decide) (by decide) (by decide) hs hs' c d
  have c13 := fun {s s' : ℤ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (c d : K) =>
    commute_xPar_outer (a := nd 1) (b := nd 3) (by decide) (by decide) (by decide) hs hs' c d
  rw [nHatE_one, weylElement_eq (nd 0), weylElement_eq (nd 1), weylElement_eq (nd 3), xOuter,
    xOuter]
  exact mul_rearrange_three (c01 n p (-1) 1) (c01 p p 1 1) (c01 p n 1 (-1)) (c03 n p (-1) 1)
    (c13 n p (-1) 1) (c03 p p 1 1) (c13 p p 1 1) (c03 p n 1 (-1)) (c13 p n 1 (-1))

theorem nHatE_mem
    (i : Fin (Tag.rank .G2)) : nHatE K i ∈ twistedGroup σ := by
  have hp : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hn : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have h1 : σ (1 : K) = 1 := map_one σ
  have h2 : σ (-1 : K) = -1 := by rw [map_neg, map_one]
  have hr0 : IsRoot .G2 ((1 : ℤ) • Pi.single (ng 0) 1) := by rw [one_smul]; exact .basis _
  have hr0' : IsRoot .G2 ((-1 : ℤ) • Pi.single (ng 0) 1) := by
    rw [neg_one_smul]; exact isRoot_neg_single _ _
  have hr1 : IsRoot .G2 ((1 : ℤ) • Pi.single (ng 1) 1) := by rw [one_smul]; exact .basis _
  have hr1' : IsRoot .G2 ((-1 : ℤ) • Pi.single (ng 1) 1) := by
    rw [neg_one_smul]; exact isRoot_neg_single _ _
  match i with
  | ⟨0, _⟩ =>
    rw [nHatE_zero_eq]
    have hx := twistedRootSubgroupD4_le_twistedGroup σ hr0 (xPar_two_mem σ hp h1)
    have hy := twistedRootSubgroupD4_le_twistedGroup σ hr0' (xPar_two_mem σ hn h2)
    exact mul_mem (mul_mem hx hy) hx
  | ⟨1, _⟩ =>
    rw [nHatE_one_eq]
    have hx := twistedRootSubgroupD4_le_twistedGroup σ hr1
      (xOuter_mem σ hp (c := 1) (by rw [h1, h1, h1]))
    have hy := twistedRootSubgroupD4_le_twistedGroup σ hr1'
      (xOuter_mem σ hn (c := -1) (by rw [h2, h2, h2]))
    rw [h1, h1] at hx
    rw [h2, h2] at hy
    exact mul_mem (mul_mem hx hy) hx

@[expose] def nHat
    (i : Fin (Tag.rank .G2)) : twistedGroup σ := ⟨nHatE K i, nHatE_mem σ i⟩

theorem nHat_val
    (i : Fin (Tag.rank .G2)) : (nHat σ i : adjointGroup d4 K) = nHatE K i := rfl

@[expose] def fixedUnits : Subgroup Kˣ :=
  MonoidHom.eqLocus (Units.map σ.toMonoidHom) (MonoidHom.id Kˣ)

theorem mem_fixedUnits {t : Kˣ} : t ∈ fixedUnits σ ↔ σ t = t := by
  change Units.map σ.toMonoidHom t = t ↔ _
  rw [Units.ext_iff, Units.coe_map]
  rfl

@[expose] def hLongHom
    : fixedUnits σ →* adjointGroup d4 K :=
  (torusHom (τ := d4) K (nd 2)).comp (fixedUnits σ).subtype

@[expose] def hShortHom :
    Kˣ →* adjointGroup d4 K where
  toFun t := torusElement d4 K (nd 0) t * torusElement d4 K (nd 1) (Units.map σ.toMonoidHom t) *
    torusElement d4 K (nd 3) (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t))
  map_one' := by
    simp only [map_one]
    rw [show torusElement d4 K (nd 0) 1 = 1 from (torusHom (τ := d4) K (nd 0)).map_one,
      show torusElement d4 K (nd 1) 1 = 1 from (torusHom (τ := d4) K (nd 1)).map_one,
      show torusElement d4 K (nd 3) 1 = 1 from (torusHom (τ := d4) K (nd 3)).map_one]
    simp
  map_mul' s t := by
    have hm : ∀ (a : Fin d4.rank) (u v : Kˣ),
        torusElement d4 K a (u * v) = torusElement d4 K a u * torusElement d4 K a v :=
      fun a u v => (torusHom (τ := d4) K a).map_mul u v
    simp only [map_mul, hm]
    have c := fun (a b : Fin d4.rank) (u v : Kˣ) => (torusElement_commute a b u v).eq
    calc torusElement d4 K (nd 0) s * torusElement d4 K (nd 0) t *
          (torusElement d4 K (nd 1) (Units.map σ.toMonoidHom s) *
            torusElement d4 K (nd 1) (Units.map σ.toMonoidHom t)) *
          (torusElement d4 K (nd 3) (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom s)) *
            torusElement d4 K (nd 3) (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t))) =
        torusElement d4 K (nd 0) s * (torusElement d4 K (nd 0) t *
          torusElement d4 K (nd 1) (Units.map σ.toMonoidHom s)) *
          torusElement d4 K (nd 1) (Units.map σ.toMonoidHom t) *
          (torusElement d4 K (nd 3) (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom s)) *
            torusElement d4 K (nd 3) (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t))) := by
          group
      _ = _ := by
        rw [c (nd 0) (nd 1)]
        simp only [mul_assoc]
        rw [← mul_assoc (torusElement d4 K (nd 1) (Units.map σ.toMonoidHom t)),
          c (nd 1) (nd 3), mul_assoc, ← mul_assoc (torusElement d4 K (nd 0) t),
          c (nd 0) (nd 3)]
        simp only [mul_assoc]

theorem hShortHom_apply
    (t : Kˣ) :
    hShortHom σ t = torusElement d4 K (nd 0) t *
      torusElement d4 K (nd 1) (Units.map σ.toMonoidHom t) *
        torusElement d4 K (nd 3) (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)) :=
  rfl

@[expose] def hHatE :
    Fin (Tag.rank .G2) → Subgroup (adjointGroup d4 K) :=
  ![(hLongHom σ).range, (hShortHom σ).range]

@[expose] def hHat
    (i : Fin (Tag.rank .G2)) : Subgroup (twistedGroup σ) :=
  (hHatE σ i).subgroupOf (twistedGroup σ)

end CFSG.LieType.Steinberg.TwistedD4
