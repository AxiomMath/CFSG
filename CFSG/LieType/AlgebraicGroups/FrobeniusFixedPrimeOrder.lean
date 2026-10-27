module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang

import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
import CFSG.LieType.AlgebraicGroups.ToralTwistPinning
import CFSG.LieType.AlgebraicGroups.ZariskiClosureFrobenius
import CFSG.LieType.AlgebraicGroups.UnipotentFrobeniusFixed

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv

open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]
  (p : ℕ) [Fact p.Prime] [CharP k p]

omit [IsAlgClosed k] in
private theorem entrywiseFrobGL_eq_self_of_dvd {j J : ℕ} (hdvd : j ∣ J)
    {g : ModGL τ k} (hg : entrywiseFrobGL τ k p j g = g) :
    entrywiseFrobGL τ k p J g = g := by
  obtain ⟨c, rfl⟩ := hdvd
  induction c with
  | zero => rw [Nat.mul_zero, entrywiseFrobGL_zero]
  | succ c ih =>
    have h : entrywiseFrobGL τ k p (j * (c + 1)) g =
        entrywiseFrobGL τ k p j (entrywiseFrobGL τ k p (j * c) g) := by
      rw [entrywiseFrobGL_frobGL, Nat.mul_succ]
    rw [h, ih, hg]

private def frobFixedSubgroup (H : Subgroup (ModGL τ k)) (e m : ℕ) :
    Subgroup (ModGL τ k) where
  carrier := {g | g ∈ H ∧ entrywiseFrobGL τ k p (e * Nat.factorial (m + 1)) g = g}
  one_mem' := ⟨H.one_mem, map_one _⟩
  mul_mem' := by
    rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
    exact ⟨H.mul_mem haH hbH, by rw [map_mul, ha, hb]⟩
  inv_mem' := by
    rintro a ⟨haH, ha⟩
    exact ⟨H.inv_mem haH, by rw [map_inv, ha]⟩

omit [IsAlgClosed k] in
private theorem mem_frobFixedSubgroup {H : Subgroup (ModGL τ k)} {e m : ℕ}
    {g : ModGL τ k} :
    g ∈ frobFixedSubgroup (p := p) H e m ↔
      g ∈ H ∧ entrywiseFrobGL τ k p (e * Nat.factorial (m + 1)) g = g :=
  Iff.rfl

omit [IsAlgClosed k] in
private theorem finite_frobFixedSubgroup {H : Subgroup (ModGL τ k)} {e m : ℕ} (he : 1 ≤ e) :
    (frobFixedSubgroup (p := p) H e m : Set (ModGL τ k)).Finite := by
  have hpos : 0 < e * Nat.factorial (m + 1) := Nat.mul_pos (by omega) (Nat.factorial_pos _)
  have hn : 1 ≤ e * Nat.factorial (m + 1) := by omega
  exact (finite_setOf_entrywiseFrobGL_eq (p := p) (τ := τ) (k := k) hn).subset
    fun _ hg => hg.2

omit [IsAlgClosed k] in
private theorem frobFixedSubgroup_mono {H : Subgroup (ModGL τ k)} {e m : ℕ} :
    frobFixedSubgroup (p := p) H e m ≤ frobFixedSubgroup (p := p) H e (m + 1) := by
  intro g hg
  rw [mem_frobFixedSubgroup] at hg ⊢
  refine ⟨hg.1, entrywiseFrobGL_eq_self_of_dvd (p := p) ?_ hg.2⟩
  exact mul_dvd_mul_left e (Nat.factorial_dvd_factorial (Nat.le_succ (m + 1)))

omit [IsAlgClosed k] in
private theorem entrywiseFrobGL_mem_frobFixedSubgroup {H : Subgroup (ModGL τ k)} {e m : ℕ}
    {g : ModGL τ k} (hH : ∀ g ∈ H, entrywiseFrobGL τ k p e g ∈ H)
    (hg : g ∈ frobFixedSubgroup (p := p) H e m) :
    entrywiseFrobGL τ k p e g ∈ frobFixedSubgroup (p := p) H e m := by
  rw [mem_frobFixedSubgroup] at hg ⊢
  refine ⟨hH g hg.1, ?_⟩
  set n := e * Nat.factorial (m + 1)
  have h1 : entrywiseFrobGL τ k p n (entrywiseFrobGL τ k p e g) =
      entrywiseFrobGL τ k p (e + n) g := entrywiseFrobGL_frobGL (p := p) n e g
  have h2 : entrywiseFrobGL τ k p e (entrywiseFrobGL τ k p n g) =
      entrywiseFrobGL τ k p (n + e) g := entrywiseFrobGL_frobGL (p := p) e n g
  rw [h1, Nat.add_comm e n, ← h2, hg.2]

private instance finite_subgroup_of_finite (G : Type*) [Group G] [Finite G] :
    Finite (Subgroup G) := by
  classical
  have hfin : ∀ H : Subgroup G, (H : Set G).Finite := fun H => Set.toFinite (H : Set G)
  refine Finite.of_injective (fun H : Subgroup G => (hfin H).toFinset) ?_
  intro H K h
  apply SetLike.ext'
  rw [← (hfin H).coe_toFinset, ← (hfin K).coe_toFinset]
  exact congrArg (fun s : Finset G => (s : Set G)) h

private instance finite_sylow_of_finite (G : Type*) [Group G] [Finite G] :
    Finite (Sylow p G) :=
  Finite.of_injective (fun Q : Sylow p G => (Q : Subgroup G))
    fun _ _ h => Sylow.ext h

private theorem card_le_card_sylow {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} (hA : IsPGroup p A) (P : Sylow p G) :
    Nat.card A ≤ Nat.card P := by
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  calc
    Nat.card A ≤ Nat.card Q := Subgroup.card_le_of_le hQ
    _ = Nat.card P := by rw [Q.card_eq_multiplicity, P.card_eq_multiplicity]

private theorem exists_conj_of_card {G : Type*} [Group G] [Finite G]
    {P Q : Subgroup G} (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hQ : Nat.card Q = p ^ (Nat.card G).factorization p) :
    ∃ x : G, Q = P.map (MulAut.conj x).toMonoidHom := by
  classical
  let P' : Sylow p G := Sylow.ofCard P hP
  let Q' : Sylow p G := Sylow.ofCard Q hQ
  have hP' : (P' : Subgroup G) = P := Sylow.coe_ofCard P hP
  have hQ' : (Q' : Subgroup G) = Q := Sylow.coe_ofCard Q hQ
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G P' Q'
  refine ⟨x, ?_⟩
  have hxsub : ((x • P' : Sylow p G) : Subgroup G) = Q := by
    rw [← hQ']
    exact congrArg (fun S : Sylow p G => (S : Subgroup G)) hx
  rw [← hxsub, ← hP']
  exact Subgroup.pointwise_smul_def (P' : Subgroup G)

private theorem card_le_prime_pow_factorization {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} (hA : IsPGroup p A) :
    Nat.card A ≤ p ^ (Nat.card G).factorization p := by
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  calc
    Nat.card A ≤ Nat.card Q := Subgroup.card_le_of_le hQ
    _ = p ^ (Nat.card G).factorization p := Q.card_eq_multiplicity

private theorem monotone_nat_eventually_const {c : ℕ → ℕ} (hc : Monotone c) {B : ℕ}
    (hB : ∀ m, c m ≤ B) : ∃ M, ∀ m, M ≤ m → c m = c M := by
  classical
  set R : Finset ℕ := (Finset.range (B + 1)).filter fun x => ∃ m, c m = x with hR
  have hRne : R.Nonempty := by
    refine ⟨c 0, ?_⟩
    rw [hR]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hB 0)), ⟨0, rfl⟩⟩
  set L := R.max' hRne with hL
  have hLmem : L ∈ R := Finset.max'_mem R hRne
  obtain ⟨M, hM⟩ : ∃ M, c M = L := by
    rw [hR] at hLmem
    exact (Finset.mem_filter.mp hLmem).2
  have hmax : ∀ m, c m ≤ L := by
    intro m
    have hmem : c m ∈ R := by
      rw [hR]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hB m)), ⟨m, rfl⟩⟩
    have h := Finset.le_max' R (c m) hmem
    have hp : (⟨c m, hmem⟩ : R.Nonempty) = hRne := Subsingleton.elim _ _
    rw [hL, ← hp]
    exact h
  refine ⟨M, fun m hm => ?_⟩
  have hle : L ≤ c m := by rw [← hM]; exact hc hm
  exact (le_antisymm (hmax m) hle).trans hM.symm

omit [IsAlgClosed k] in
private lemma subgroupOf_map_conj_map_subtype {X P : Subgroup (ModGL τ k)} (hPX : P ≤ X)
    (x : X) :
    ((P.subgroupOf X).map (MulAut.conj x).toMonoidHom).map X.subtype =
      P.map (MulAut.conj (x : ModGL τ k)).toMonoidHom := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb
    refine Subgroup.mem_map.mpr ⟨(c : ModGL τ k), hc, ?_⟩
    exact congrArg (Subtype.val) hcb
  · rintro ⟨b, hb, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj x) ⟨b, hPX hb⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨b, hPX hb⟩, hb, rfl⟩
    · simp [MulAut.conj_apply]

private noncomputable def sylowBase (X : ℕ → Subgroup (ModGL τ k))
    (hXfin : (X 0 : Set (ModGL τ k)).Finite) :
    {P : Subgroup (ModGL τ k) // P ≤ X 0 ∧ IsPGroup p P ∧
      Nat.card P = p ^ (Nat.card (X 0)).factorization p} := by
  classical
  haveI : Finite (X 0) := hXfin.to_subtype
  let Q : Sylow p (X 0) := Classical.choice Sylow.nonempty
  refine ⟨Subgroup.map (X 0).subtype (Q : Subgroup (X 0)), ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le _
  · exact IsPGroup.map Q.isPGroup' _
  · rw [Subgroup.card_map_of_injective (X 0).subtype_injective]
    exact Q.card_eq_multiplicity

private noncomputable def sylowStep (X : ℕ → Subgroup (ModGL τ k))
    (_hXmono : ∀ m, X m ≤ X (m + 1))
    (hXfin : ∀ m, (X m : Set (ModGL τ k)).Finite) (m : ℕ)
    (Pm : {P : Subgroup (ModGL τ k) // P ≤ X m ∧ IsPGroup p P ∧
      Nat.card P = p ^ (Nat.card (X m)).factorization p}) :
    {P : Subgroup (ModGL τ k) // P ≤ X (m + 1) ∧ IsPGroup p P ∧
      Nat.card P = p ^ (Nat.card (X (m + 1))).factorization p} := by
  classical
  haveI : Finite (X (m + 1)) := (hXfin (m + 1)).to_subtype
  have hA : IsPGroup p (Pm.1.subgroupOf (X (m + 1))) :=
    Pm.2.2.1.comap_of_injective (X (m + 1)).subtype Subtype.coe_injective
  let Q : Sylow p (X (m + 1)) := Classical.choose hA.exists_le_sylow
  refine ⟨Subgroup.map (X (m + 1)).subtype (Q : Subgroup (X (m + 1))), ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le _
  · exact IsPGroup.map Q.isPGroup' _
  · rw [Subgroup.card_map_of_injective (X (m + 1)).subtype_injective]
    exact Q.card_eq_multiplicity

omit [IsAlgClosed k] [CharP k p] in
private theorem sylowStep_le (X : ℕ → Subgroup (ModGL τ k))
    (hXmono : ∀ m, X m ≤ X (m + 1))
    (hXfin : ∀ m, (X m : Set (ModGL τ k)).Finite) (m : ℕ)
    (Pm : {P : Subgroup (ModGL τ k) // P ≤ X m ∧ IsPGroup p P ∧
      Nat.card P = p ^ (Nat.card (X m)).factorization p}) :
    Pm.1 ≤ (sylowStep (p := p) X hXmono hXfin m Pm).1 := by
  classical
  intro x hx
  have hxX : x ∈ X (m + 1) := hXmono m (Pm.2.1 hx)
  have hA : IsPGroup p (Pm.1.subgroupOf (X (m + 1))) :=
    Pm.2.2.1.comap_of_injective (X (m + 1)).subtype Subtype.coe_injective
  have hxQ : (⟨x, hxX⟩ : X (m + 1)) ∈
      (Classical.choose hA.exists_le_sylow : Sylow p (X (m + 1))) :=
    Classical.choose_spec hA.exists_le_sylow hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hxX⟩, hxQ, rfl⟩

theorem exists_entrywiseFrobGL_fixed_orderOf_eq_prime
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    {Z : Subgroup (ModGL τ k)}
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))))
    {e : ℕ} (he : 1 ≤ e) (hS : ∀ g ∈ Z, entrywiseFrobGL τ k p e g ∈ Z)
    {V : Subgroup (ModGL τ k)} (hV : V ≤ closedIdentityComponent Z)
    (hVinf : (V : Set (ModGL τ k)).Infinite) (hVp : IsPGroup p V) :
    ∃ u ∈ closedIdentityComponent Z, entrywiseFrobGL τ k p e u = u ∧ orderOf u = p := by
  classical
  let H := closedIdentityComponent Z
  have hHc : IsPointClosed k (transportPoints (modGLPoint τ k) (H : Set (ModGL τ k))) :=
    isPointClosed_closedIdentityComponent hZ
  have hS1 : ∀ g ∈ Z, frobTwistGL τ k p e 1 g ∈ Z := by
    intro g hg
    simpa [frobTwistGL_apply] using hS g hg
  have hFH : ∀ g ∈ H, entrywiseFrobGL τ k p e g ∈ H := by
    intro g hg
    have h := frobTwistGL_mem_closedIdentityComponent (p := p) e 1 hS1 hg
    simpa [frobTwistGL_apply] using h
  let X : ℕ → Subgroup (ModGL τ k) := fun m => frobFixedSubgroup (p := p) H e m
  have hXleH : ∀ m, X m ≤ H := by
    intro m g hg
    exact (mem_frobFixedSubgroup (p := p)).mp hg |>.1
  have hXmono : ∀ m, X m ≤ X (m + 1) := fun m => frobFixedSubgroup_mono (p := p)
  have hXmonoNat : Monotone X := monotone_nat_of_le_succ hXmono
  have hXfin : ∀ m, (X m : Set (ModGL τ k)).Finite := fun m =>
    finite_frobFixedSubgroup (p := p) he
  have hXunion : ∀ g ∈ H, ∃ m, g ∈ X m := by
    intro g hg
    obtain ⟨s, hs1, hs⟩ := exists_entrywiseFrobGL_eq_self (p := p) halg g
    have hdiv : s ∣ e * Nat.factorial (s + 1) := by
      have h1 : s ∣ Nat.factorial (s + 1) := Nat.dvd_factorial (by omega) (by omega)
      exact h1.trans (dvd_mul_left _ e)
    exact ⟨s, (mem_frobFixedSubgroup (p := p)).mpr ⟨hg, hs _ hdiv⟩⟩
  let P : (m : ℕ) → {P : Subgroup (ModGL τ k) // P ≤ X m ∧ IsPGroup p P ∧
      Nat.card P = p ^ (Nat.card (X m)).factorization p} :=
    Nat.rec (sylowBase (p := p) X (hXfin 0))
      (fun m Pm => sylowStep (p := p) X hXmono hXfin m Pm)
  have hPX : ∀ m, (P m).1 ≤ X m := fun m => (P m).2.1
  have hPp : ∀ m, IsPGroup p (P m).1 := fun m => (P m).2.2.1
  have hPcard : ∀ m, Nat.card (P m).1 = p ^ (Nat.card (X m)).factorization p :=
    fun m => (P m).2.2.2
  have hPmono : ∀ m, (P m).1 ≤ (P (m + 1)).1 := by
    intro m
    change (P m).1 ≤ (sylowStep (p := p) X hXmono hXfin m (P m)).1
    exact sylowStep_le (p := p) X hXmono hXfin m (P m)
  let Pbar : ℕ → Subgroup (ModGL τ k) := fun m => (P m).1
  have hPbarX : ∀ m, Pbar m ≤ X m := fun m => hPX m
  have hPbarp : ∀ m, IsPGroup p (Pbar m) := fun m => hPp m
  have hPbarcard : ∀ m, Nat.card (Pbar m) =
      p ^ (Nat.card (X m)).factorization p := fun m => hPcard m
  have hPbar_mono : Monotone Pbar := monotone_nat_of_le_succ fun m => hPmono m
  let PInf : Subgroup (ModGL τ k) := ⨆ m, Pbar m
  have hPbar_le_PInf : ∀ m, Pbar m ≤ PInf := fun m => le_iSup Pbar m
  have hPInfmem : ∀ {g : ModGL τ k}, g ∈ PInf ↔ ∃ m, g ∈ Pbar m := by
    intro g
    change g ∈ ⨆ m, Pbar m ↔ ∃ m, g ∈ Pbar m
    exact Subgroup.mem_iSup_of_directed hPbar_mono.directed_le
  have hPInfH : PInf ≤ H := iSup_le fun m => (hPbarX m).trans (hXleH m)
  have hPInfinf : (PInf : Set (ModGL τ k)).Infinite := by
    intro hfin
    have : Finite PInf := hfin.to_subtype
    let W : ℕ → Subgroup (ModGL τ k) := fun m => V ⊓ X m
    have hVXfin : ∀ m, Finite ↥(W m) := fun m =>
      ((hXfin m).subset fun _ hg => hg.2).to_subtype
    have hcard_bdd : ∀ m, Nat.card (W m) ≤ Nat.card PInf := by
      intro m
      have : Finite ↥(X m) := (hXfin m).to_subtype
      have hA : IsPGroup p (W m) := hVp.to_inf_left
      have hcard1 : Nat.card (W m) ≤ p ^ (Nat.card (X m)).factorization p := by
        have hcardeq : Nat.card (W m) =
            Nat.card ((W m).subgroupOf (X m)) := by
          calc
            Nat.card (W m) = Nat.card (((W m).subgroupOf (X m)).map (X m).subtype) := by
              rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
            _ = Nat.card ((W m).subgroupOf (X m)) := Subgroup.card_subtype _ _
        rw [hcardeq]
        exact card_le_prime_pow_factorization (p := p)
          (hA.comap_of_injective (X m).subtype Subtype.coe_injective)
      have hcard2 : p ^ (Nat.card (X m)).factorization p = Nat.card (Pbar m) :=
        (hPbarcard m).symm
      have hcard3 : Nat.card (Pbar m) ≤ Nat.card PInf :=
        Subgroup.card_le_of_le (hPbar_le_PInf m)
      omega
    have hW_mono : Monotone W := by
      intro m n hmn
      exact inf_le_inf_left V (hXmonoNat hmn)
    have hc_mono : Monotone fun m => Nat.card (W m) := by
      intro m n hmn
      have : Finite ↥(W n) := hVXfin n
      exact Subgroup.card_le_of_le (hW_mono hmn)
    obtain ⟨M₀, hM₀⟩ := monotone_nat_eventually_const hc_mono hcard_bdd
    have hWstab : ∀ m, M₀ ≤ m → W m = W M₀ := by
      intro m hm
      have hle : W M₀ ≤ W m := hW_mono hm
      have hcard : Nat.card (W M₀) = Nat.card (W m) := by
        rw [hM₀ m hm]
      by_contra hne
      have hlt : W M₀ < W m := lt_of_le_of_ne hle (Ne.symm hne)
      have : Finite ↥(W m) := hVXfin m
      have := Subgroup.card_lt_of_lt hlt
      omega
    have hVsub : (V : Set (ModGL τ k)) ⊆ (W M₀ : Set (ModGL τ k)) := by
      intro g hg
      obtain ⟨m, hmX⟩ := hXunion g (hV hg)
      have hmk : W m ≤ W (max m M₀) := hW_mono (le_max_left m M₀)
      have hk : W (max m M₀) = W M₀ := hWstab _ (le_max_right m M₀)
      have hmem : g ∈ W (max m M₀) := hmk ⟨hg, hmX⟩
      rwa [hk] at hmem
    have hVeq : V = W M₀ := le_antisymm hVsub inf_le_left
    have hVfin : (V : Set (ModGL τ k)).Finite := by
      rw [hVeq]
      exact (hXfin M₀).subset fun _ hg => hg.2
    exact hVinf hVfin
  obtain ⟨U, hPInfU, hUc, hUmin, -⟩ := exists_isPointClosed_subgroup_closure PInf
  have hUH : U ≤ H := hUmin (H : Set (ModGL τ k)) hHc fun g hg => hPInfH hg
  have hUinf : (U : Set (ModGL τ k)).Infinite :=
    Set.Infinite.mono (fun g hg => hPInfU hg) hPInfinf
  have hUpow : ∀ u ∈ U, u ^ p ^ Fintype.card (Label τ) = 1 := by
    have hPInfpow : (PInf : Set (ModGL τ k)) ⊆
        {g : ModGL τ k | g ^ p ^ Fintype.card (Label τ) = 1} := by
      intro g hg
      change g ∈ PInf at hg
      rw [hPInfmem] at hg
      obtain ⟨m, hgm⟩ := hg
      obtain ⟨k, hk⟩ := hPbarp m ⟨g, hgm⟩
      exact pow_pow_card_label_eq_one (p := p) (by simpa using hk)
    intro u hu
    exact hUmin _ (isPointClosed_setOf_pow_eq_one (m := p ^ Fintype.card (Label τ)))
      hPInfpow hu
  have hconj : ∀ m, ∃ x ∈ X m, (Pbar m).map (entrywiseFrobGL τ k p e) =
      (Pbar m).map (MulAut.conj x).toMonoidHom := by
    intro m
    have : Finite ↥(X m) := (hXfin m).to_subtype
    have hBle : (Pbar m).map (entrywiseFrobGL τ k p e) ≤ X m := by
      rintro - ⟨a, ha, rfl⟩
      exact entrywiseFrobGL_mem_frobFixedSubgroup (p := p) hFH (hPbarX m ha)
    have hAcard : Nat.card ((Pbar m).subgroupOf (X m)) =
        p ^ (Nat.card (X m)).factorization p := by
      calc
        Nat.card ((Pbar m).subgroupOf (X m)) =
            Nat.card (((Pbar m).subgroupOf (X m)).map (X m).subtype) :=
          (Subgroup.card_subtype (X m) ((Pbar m).subgroupOf (X m))).symm
        _ = Nat.card (Pbar m) := by rw [Subgroup.map_subgroupOf_eq_of_le (hPbarX m)]
        _ = p ^ (Nat.card (X m)).factorization p := hPbarcard m
    have hBcard : Nat.card (((Pbar m).map (entrywiseFrobGL τ k p e)).subgroupOf (X m)) =
        p ^ (Nat.card (X m)).factorization p := by
      calc
        Nat.card (((Pbar m).map (entrywiseFrobGL τ k p e)).subgroupOf (X m)) =
            Nat.card ((((Pbar m).map (entrywiseFrobGL τ k p e)).subgroupOf (X m)).map
              (X m).subtype) :=
          (Subgroup.card_subtype (X m)
            (((Pbar m).map (entrywiseFrobGL τ k p e)).subgroupOf (X m))).symm
        _ = Nat.card ((Pbar m).map (entrywiseFrobGL τ k p e)) := by
          rw [Subgroup.map_subgroupOf_eq_of_le hBle]
        _ = Nat.card (Pbar m) :=
          Subgroup.card_map_of_injective (entrywiseFrobGL_injective (p := p) e)
        _ = p ^ (Nat.card (X m)).factorization p := hPbarcard m
    obtain ⟨x, hx⟩ := exists_conj_of_card (p := p) (G := X m) hAcard hBcard
    refine ⟨(x : ModGL τ k), x.2, ?_⟩
    have h := congrArg (fun S : Subgroup (X m) => S.map (X m).subtype) hx
    have hBmap : (((Pbar m).map (entrywiseFrobGL τ k p e)).subgroupOf (X m)).map
        (X m).subtype = (Pbar m).map (entrywiseFrobGL τ k p e) :=
      Subgroup.map_subgroupOf_eq_of_le hBle
    have hAmap : ((((Pbar m).subgroupOf (X m)).map (MulAut.conj x).toMonoidHom).map
        (X m).subtype) =
        (Pbar m).map (MulAut.conj (x : ModGL τ k)).toMonoidHom :=
      subgroupOf_map_conj_map_subtype (hPX := hPbarX m) x
    rw [hBmap, hAmap] at h
    exact h
  choose xm hxm_mem hxm_conj using hconj
  let T : ℕ → Set (ModGL τ k) := fun m =>
    (H : Set (ModGL τ k)) ∩ ⋂ a : Pbar m,
      {g : ModGL τ k | g⁻¹ * entrywiseFrobGL τ k p e (a : ModGL τ k) * g ∈ U}
  have hTc : ∀ m, IsPointClosed k (transportPoints (modGLPoint τ k) (T m)) := by
    intro m
    refine isPointClosed_inter hHc ?_
    refine isPointClosed_iInter fun a => ?_
    exact isPointClosed_preimage_inv_mul_mul
      (b := entrywiseFrobGL τ k p e (a : ModGL τ k)) hUc
  have hTanti : Antitone T := by
    intro m n hmn g hg
    simp only [T, Set.mem_inter_iff, Set.mem_iInter] at hg ⊢
    refine ⟨hg.1, ?_⟩
    intro a
    exact hg.2 ⟨(a : ModGL τ k), hPbar_mono hmn a.2⟩
  have hTne : ∀ m, xm m ∈ T m := by
    intro m
    simp only [T, Set.mem_inter_iff, Set.mem_iInter]
    refine ⟨hXleH m (hxm_mem m), ?_⟩
    intro a
    have hmem : entrywiseFrobGL τ k p e (a : ModGL τ k) ∈
        (Pbar m).map (entrywiseFrobGL τ k p e) :=
      Subgroup.mem_map.mpr ⟨(a : ModGL τ k), a.2, rfl⟩
    rw [hxm_conj m] at hmem
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hmem
    have hba' : xm m * b * (xm m)⁻¹ = entrywiseFrobGL τ k p e (a : ModGL τ k) := by
      simpa [MulAut.conj_apply] using hba
    have hbU : b ∈ U := hPInfU (hPbar_le_PInf m hb)
    have hEq : (xm m)⁻¹ * entrywiseFrobGL τ k p e (a : ModGL τ k) * xm m = b := by
      rw [← hba']
      group
    change (xm m)⁻¹ * entrywiseFrobGL τ k p e (a : ModGL τ k) * xm m ∈ U
    rwa [hEq]
  obtain ⟨M, hM⟩ := exists_antitone_isPointClosed_stabilizes hTanti hTc
  have hxT : ∀ m, xm M ∈ T m := by
    intro m
    by_cases hm : m ≤ M
    · exact hTanti hm (hTne M)
    · have hMm : M ≤ m := by omega
      rw [hM m hMm]
      exact hTne M
  let S : Set (ModGL τ k) :=
    entrywiseFrobGL τ k p e ⁻¹'
      ((fun h => (xm M)⁻¹ * h * xm M) ⁻¹' (U : Set (ModGL τ k)))
  have hSc : IsPointClosed k (transportPoints (modGLPoint τ k) S) :=
    isPointClosed_preimage_entrywiseFrobGL (p := p) e
      (isPointClosed_preimage_mul_mul (x := (xm M)⁻¹) (y := xm M) hUc)
  have hPInfS : (PInf : Set (ModGL τ k)) ⊆ S := by
    intro g hg
    have hg' : g ∈ PInf := hg
    rw [hPInfmem] at hg'
    obtain ⟨m, hgm⟩ := hg'
    have hmemT : xm M ∈ T m := hxT m
    simp only [T, Set.mem_inter_iff, Set.mem_iInter] at hmemT
    exact hmemT.2 ⟨g, hgm⟩
  have hUS : (U : Set (ModGL τ k)) ⊆ S := hUmin S hSc hPInfS
  have hxU : ∀ u ∈ U, (xm M)⁻¹ * entrywiseFrobGL τ k p e u * xm M ∈ U := by
    intro u hu
    exact hUS hu
  obtain ⟨ζ, hζH, hζ⟩ := exists_inv_mul_frobTwistGL_closedIdentityComponent (p := p)
    hZ he 1 hS1 ((xm M)⁻¹) (H.inv_mem (hXleH M (hxm_mem M)))
  have hζ' : ζ⁻¹ * entrywiseFrobGL τ k p e ζ = (xm M)⁻¹ := by
    simpa [frobTwistGL_apply] using hζ
  have hFζ : entrywiseFrobGL τ k p e ζ = ζ * (xm M)⁻¹ := by
    rw [← hζ']
    group
  let U' : Subgroup (ModGL τ k) := U.map (MulAut.conj ζ).toMonoidHom
  have hU'c : IsPointClosed k (transportPoints (modGLPoint τ k) (U' : Set (ModGL τ k))) := by
    have hset : (U' : Set (ModGL τ k)) =
        (fun g => ζ⁻¹ * g * ζ) ⁻¹' (U : Set (ModGL τ k)) := by
      ext g
      constructor
      · rintro ⟨u, hu, rfl⟩
        change ζ⁻¹ * (MulAut.conj ζ u) * ζ ∈ U
        have hval : ζ⁻¹ * (MulAut.conj ζ u) * ζ = u := by
          rw [MulAut.conj_apply]
          group
        rwa [hval]
      · intro hg
        refine ⟨ζ⁻¹ * g * ζ, hg, ?_⟩
        change MulAut.conj ζ (ζ⁻¹ * g * ζ) = g
        rw [MulAut.conj_apply]
        group
    rw [hset]
    exact isPointClosed_preimage_mul_mul (x := ζ⁻¹) (y := ζ) hUc
  have hU'leH : U' ≤ H := by
    rintro - ⟨u, hu, rfl⟩
    have huH : u ∈ H := hUH hu
    have hζi : ζ⁻¹ ∈ H := H.inv_mem hζH
    have : ζ * u * ζ⁻¹ ∈ H := H.mul_mem (H.mul_mem hζH huH) hζi
    simpa [MulAut.conj_apply] using this
  have hU'inf : (U' : Set (ModGL τ k)).Infinite := by
    have hinj : Set.InjOn (fun u : ModGL τ k => ζ * u * ζ⁻¹) (U : Set (ModGL τ k)) := by
      intro a _ b _ hab
      have := congrArg (fun x => ζ⁻¹ * x * ζ) hab
      simpa [mul_assoc] using this
    have h := Set.Infinite.image hinj hUinf
    have himg : ((fun u : ModGL τ k => ζ * u * ζ⁻¹) '' (U : Set (ModGL τ k))) =
        (MulAut.conj ζ) '' (U : Set (ModGL τ k)) := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, by rw [MulAut.conj_apply]⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, by rw [MulAut.conj_apply]⟩
    rw [himg] at h
    simpa [U'] using h
  have hU'pow : ∀ g ∈ U', g ^ p ^ Fintype.card (Label τ) = 1 := by
    rintro - ⟨u, hu, rfl⟩
    change ((MulEquiv.toMonoidHom (MulAut.conj ζ)) u) ^
      (p ^ Fintype.card (Label τ)) = 1
    rw [← map_pow, hUpow u hu, map_one]
  have hFU' : ∀ g ∈ U', entrywiseFrobGL τ k p e g ∈ U' := by
    rintro - ⟨u, hu, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(xm M)⁻¹ * entrywiseFrobGL τ k p e u * xm M, hxU u hu, ?_⟩
    change ζ * ((xm M)⁻¹ * entrywiseFrobGL τ k p e u * xm M) * ζ⁻¹ =
      entrywiseFrobGL τ k p e (ζ * u * ζ⁻¹)
    rw [map_mul, map_mul, map_inv, hFζ]
    group
  let U'c := closedIdentityComponent U'
  have hU'cc : IsPointClosed k (transportPoints (modGLPoint τ k) (U'c : Set (ModGL τ k))) :=
    isPointClosed_closedIdentityComponent hU'c
  have hU'ci : IsPointIrreducible k (transportPoints (modGLPoint τ k) (U'c : Set (ModGL τ k))) :=
    isPointIrreducible_closedIdentityComponent U'
  have hFU'c : ∀ g ∈ U'c, entrywiseFrobGL τ k p e g ∈ U'c := by
    have hS1' : ∀ g ∈ U', frobTwistGL τ k p e 1 g ∈ U' := by
      intro g hg
      simpa [frobTwistGL_apply] using hFU' g hg
    intro g hg
    have h := frobTwistGL_mem_closedIdentityComponent (p := p) e 1 hS1' hg
    simpa [frobTwistGL_apply] using h
  have hU'cpow : ∀ u ∈ U'c, u ^ p ^ Fintype.card (Label τ) = 1 := by
    intro u hu
    exact hU'pow u (closedIdentityComponent_le U' hu)
  have hU'cne : U'c ≠ ⊥ := by
    intro hbot
    have hfinidx : (U'c.subgroupOf U').FiniteIndex := closedIdentityComponent_finiteIndex U'
    rw [hbot, Subgroup.bot_subgroupOf] at hfinidx
    have hfin : Finite U' :=
      (Subgroup.finite_iff_finite_and_finiteIndex (⊥ : Subgroup U')).2
        ⟨inferInstance, hfinidx⟩
    exact hU'inf hfin
  obtain ⟨u, huU'c, hu_ne, hu_fixed⟩ :=
    exists_ne_one_entrywiseFrobGL_eq_self_of_unipotent (p := p)
      hU'cc hU'ci he hFU'c hU'cpow hU'cne
  have huH : u ∈ H := hU'leH (closedIdentityComponent_le U' huU'c)
  have huPow : u ^ p ^ Fintype.card (Label τ) = 1 := hU'cpow u huU'c
  have hdvd : orderOf u ∣ p ^ Fintype.card (Label τ) :=
    orderOf_dvd_iff_pow_eq_one.mpr huPow
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdvd
  have hbne : b ≠ 0 := by
    intro hb0
    apply hu_ne
    exact orderOf_eq_one_iff.mp (by rw [hb, hb0, pow_zero])
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hvd : p ∣ orderOf u := by
    rw [hb]
    exact dvd_pow_self p (Nat.succ_ne_zero c)
  have hord0 : orderOf u ≠ 0 := by
    rw [hb]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  exact ⟨u ^ (orderOf u / p), H.pow_mem huH (orderOf u / p), by rw [map_pow, hu_fixed],
    orderOf_pow_orderOf_div hord0 hvd⟩

end CFSG.LieType.AlgebraicGroups
