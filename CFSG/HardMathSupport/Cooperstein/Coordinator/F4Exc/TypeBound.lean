module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.PairBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.OneDigit
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Translates
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.CopiesDim

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

section TypeBound


@[expose] def F4Surv (K : Type) [Field K] {k : Type} [Field k] [Algebra K k]
    (χ : adjointGroup .F4 K → k) (J : Finset (Fin Tag.F4.rank)) : Prop :=
  ∃ (b : ℕ) (s : Fin Tag.F4.rank), (s.val = 0 ∨ s.val = 3) ∧ J = Finset.univ.erase s ∧
    ∀ (i : Fin Tag.F4.rank) (t : Kˣ),
      χ (dC .F4 K i t) = (algebraMap K k (t : K)) ^ (if i = s then 2 ^ b else 0)

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem no_J_univ4 {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .F4 K) V} (hρ : IsSimpleRep ρ)
    (hinj : Function.Injective ρ) {y : V} {χ : adjointGroup .F4 K → k}
    {J : Finset (Fin Tag.F4.rank)} (ht : IsChevType .F4 K 2 exists_weyl_neg_F4' ρ y χ J)
    (hJ : J = Finset.univ) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hχi : ∀ i t, χ (dC .F4 K i t) = 1 := fun i t =>
    ((ht.2.2.2 i).1 (hJ ▸ Finset.mem_univ i)).1 t
  have hy1 : ∀ i t, ρ (dC .F4 K i t) y = y := fun i t => by
    rw [ht.2.2.1 _ (dC_mem_H i t), hχi, one_smul]
  have hHy : ∀ h ∈ (chevDatum .F4 K 2 exists_weyl_neg_F4').H, ρ h y = y := by
    intro h hh
    have hh' : (h : ModGL .F4 K) ∈ torusGroup .F4 K := hh
    have key : ∀ g ∈ torusGroup .F4 K, ∃ hg : g ∈ adjointGroup .F4 K, ρ ⟨g, hg⟩ y = y := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨⟨i, t⟩, rfl⟩ := hx
        exact ⟨torusElt_mem_adjointGroup i t, hy1 i t⟩
      | one => exact ⟨one_mem _, by show ρ 1 y = y; rw [map_one, Module.End.one_apply]⟩
      | mul a b _ _ ha hb =>
        obtain ⟨ha1, ha2⟩ := ha
        obtain ⟨hb1, hb2⟩ := hb
        refine ⟨mul_mem ha1 hb1, ?_⟩
        have : (⟨a * b, mul_mem ha1 hb1⟩ : adjointGroup .F4 K) = ⟨a, ha1⟩ * ⟨b, hb1⟩ := rfl
        rw [this, ← act_mul, hb2, ha2]
      | inv a _ ha =>
        obtain ⟨ha1, ha2⟩ := ha
        refine ⟨inv_mem ha1, ?_⟩
        have : (⟨a⁻¹, inv_mem ha1⟩ : adjointGroup .F4 K) = (⟨a, ha1⟩ : adjointGroup .F4 K)⁻¹ := rfl
        rw [this]
        have h2 : ρ (⟨a, ha1⟩ : adjointGroup .F4 K)⁻¹ (ρ ⟨a, ha1⟩ y) = y := by
          rw [act_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha2] at h2
    obtain ⟨hg, hρg⟩ := key _ hh'
    exact hρg
  have hχ1 : ∀ h ∈ (chevDatum .F4 K 2 exists_weyl_neg_F4').H, χ h = 1 := by
    intro h hh
    have h1 := ht.2.2.1 h hh
    rw [hHy h hh] at h1
    exact (smul_left_injective k ht.2.1 (show χ h • y = (1 : k) • y by rw [one_smul]; exact h1.symm))
  set ρ0 : Representation k (adjointGroup .F4 K) (Unit →₀ k) :=
    Representation.trivial k _ (Unit →₀ k) with hρ0def
  have hρ0 : IsSimpleRep ρ0 := by
    refine ⟨⟨⟨0, Finsupp.single () 1, fun h => by simpa using congrArg (fun f => f ()) h⟩⟩,
      fun W _ => ?_⟩
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    obtain ⟨f, hfW, hf0⟩ := (Submodule.ne_bot_iff W).1 hW
    have hf : f = f () • Finsupp.single () 1 := Finsupp.ext fun u => by cases u; simp
    have hc : f () ≠ 0 := fun h => hf0 (by rw [hf, h, zero_smul])
    generalize f () = c at hf hc
    have hs : Finsupp.single () (1 : k) ∈ W := by
      have := W.smul_mem c⁻¹ hfW
      rwa [hf, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    refine eq_top_iff.2 fun g _ => ?_
    have : g = g () • Finsupp.single () 1 := Finsupp.ext fun u => by cases u; simp
    rw [this]
    exact Submodule.smul_mem _ _ hs
  have ht0 : IsChevType .F4 K 2 exists_weyl_neg_F4' ρ0 (Finsupp.single () (1 : k)) χ J := by
    refine ⟨fun u _ => by simp [hρ0def], fun h => by simpa using congrArg (fun f => f ()) h,
      fun h hh => ?_, fun i => ?_⟩
    · simp [hρ0def, hχ1 h hh]
    · refine ⟨fun _ => ⟨hχi i, ?_⟩, fun _ => hJ ▸ Finset.mem_univ i⟩
      letI : Fintype K := Fintype.ofFinite K
      rw [heckeT_chevDatum]
      simp only [hρ0def, Representation.trivial_apply, Finset.sum_const, Finset.card_univ]
      rw [← Nat.card_eq_fintype_card, hK, ← Nat.cast_smul_eq_nsmul k]
      have h0' : ((2 ^ n : ℕ) : k) = 0 := by
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
        rw [pow_succ]; push_cast; rw [CharTwo.two_eq_zero, mul_zero]
      rw [h0', zero_smul]
  obtain ⟨β, hβ⟩ := iso_of_isChevType hρ hρ0 ht ht0
  have hid : ∀ g v, ρ g v = v := fun g v => by
    apply β.injective
    rw [hβ]
    simp [hρ0def]
  have h1 : xC .F4 K (f4n 0) 1 = 1 :=
    hinj (by ext v; rw [hid, map_one, Module.End.one_apply])
  exact xC_ne_one (f4n 0) 1 h1

theorem weyl_smul_smulF
    (w : WeylGroup .F4) (A : ℤ) (x : Fin Tag.F4.rank → ℤ) : w • (A • x) = A • (w • x) := by
  have := weyl_smul_combF w A 0 x 0
  simpa using this

theorem lamF_single (s : Fin Tag.F4.rank) (A : ℕ) :
    lamF (fun i => if i = s then A else 0) = (A : ℤ) • f4Omega s := by
  funext l
  simp [lamF, Finset.sum_ite_eq']

theorem f4TypeBound {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
      (ρ : Representation k (adjointGroup .F4 K) (Fin m → k)) (y : Fin m → k)
      (χ : adjointGroup .F4 K → k) (J : Finset (Fin Tag.F4.rank)) (g : ℕ),
      IsSimpleRep ρ → Function.Injective ρ →
      IsChevType .F4 K 2 exists_weyl_neg_F4' ρ y χ J → 1 ≤ g → g ∣ n →
      (∀ (i : Fin Tag.F4.rank) (t : Kˣ), χ (dC .F4 K i t) ^ (2 ^ g) = χ (dC .F4 K i t)) →
      52 * (n / g) + 1 ≤ m ∨ (n / g = 1 ∧ F4Surv K χ J) := by
  intro k _ _ _ _ m ρ y χ J g hρ hinj ht hg hgn hper
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Module.finrank k (Fin m → k) = m := Module.finrank_fin_fun k
  have hJne : J ≠ Finset.univ := fun h => no_J_univ4 hn hK hρ hinj ht h
  have hex : ∃ s, s ∉ J := by
    by_contra h
    push Not at h
    exact hJne (Finset.eq_univ_of_forall h)
  rcases Nat.lt_or_ge (n / g) 2 with h1 | h2
  ·
    have hpos : 0 < n / g := Nat.div_pos (Nat.le_of_dvd (by omega) hgn) (by omega)
    have ht1 : n / g = 1 := by omega
    rw [ht1]
    by_cases hmid : ∃ s : Fin Tag.F4.rank, (s.val = 1 ∨ s.val = 2) ∧ s ∉ J
    · obtain ⟨s, hs12, hsJ⟩ := hmid
      obtain ⟨w, hw⟩ := exists_orbit_mid s hs12
      have := card_le_finrank_of_isChevType hρ ht hsJ (reflect_f4Omega s) w hw
      rw [hfin] at this
      left; omega
    push Not at hmid
    by_cases hends : f4n 0 ∉ J ∧ f4n 3 ∉ J
    · obtain ⟨w, hw⟩ := exists_orbit_ends
      have := card_le_finrank_of_isChevType_supp hρ ht (S := {f4n 0, f4n 3}) (by
        intro s hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · exact hends.1
        · exact hends.2) (v := omEnds) (fun j hj => reflect_omEnds j (by
          by_contra hcon
          push Not at hcon
          apply hj
          simp only [Finset.mem_insert, Finset.mem_singleton]
          have : j.val < 4 := j.2
          rcases (by omega : j.val = 0 ∨ j.val = 3) with h | h
          · left; exact Fin.ext h
          · right; exact Fin.ext h)) w hw
      rw [hfin] at this
      left; omega
    obtain ⟨s, hs03, hsJ, hrest⟩ : ∃ s : Fin Tag.F4.rank, (s.val = 0 ∨ s.val = 3) ∧ s ∉ J ∧
        ∀ i, i ≠ s → i ∈ J := by
      obtain ⟨s, hsJ⟩ := hex
      have hs03 : s.val = 0 ∨ s.val = 3 := by
        by_contra hcon
        push Not at hcon
        have : s.val = 1 ∨ s.val = 2 := by have h4 : s.val < 4 := s.2; omega
        exact hsJ (hmid s this)
      refine ⟨s, hs03, hsJ, fun i hi => ?_⟩
      by_contra hiJ
      apply hends
      rcases hs03 with h0 | h3
      · have hs0 : s = f4n 0 := Fin.ext h0
        subst hs0
        have : i.val = 3 := by
          by_contra hne
          have h12 : i.val = 1 ∨ i.val = 2 := by
            have h4 : i.val < 4 := i.2
            have hne0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            omega
          exact hiJ (hmid i h12)
        have : i = f4n 3 := Fin.ext this
        subst this
        exact ⟨hsJ, hiJ⟩
      · have hs3 : s = f4n 3 := Fin.ext h3
        subst hs3
        have : i.val = 0 := by
          by_contra hne
          have h12 : i.val = 1 ∨ i.val = 2 := by
            have h4 : i.val < 4 := i.2
            have hne3 : i.val ≠ 3 := fun h => hi (Fin.ext h)
            omega
          exact hiJ (hmid i h12)
        have : i = f4n 0 := Fin.ext this
        subst this
        exact ⟨hiJ, hsJ⟩
    obtain ⟨J', hJ'n, hχs, hdim, hJ0, hwt⟩ := string_of_highest (hw := exists_weyl_neg_F4') hK hρ ht s
    have hne := string_nonempty hn hK ht hsJ hχs hJ0
    have hJeq : J = Finset.univ.erase s := by
      ext i
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro hi rfl; exact hsJ hi
      · exact fun hi => hrest i hi
    have hχother : ∀ i, i ≠ s → ∀ t : Kˣ, χ (dC .F4 K i t) = 1 := fun i hi t =>
      ((ht.2.2.2 i).1 (hrest i hi)).1 t
    have hcard1 : 1 ≤ J'.card := Finset.card_pos.2 hne
    rcases Nat.lt_or_ge J'.card 3 with hc3 | hc3
    · rcases (by omega : J'.card = 1 ∨ J'.card = 2) with hc1 | hc2
      · right
        obtain ⟨b, hb⟩ := Finset.card_eq_one.1 hc1
        refine ⟨rfl, b, s, hs03, hJeq, fun i t => ?_⟩
        by_cases hi : i = s
        · subst hi
          rw [if_pos rfl, hχs t, hb, Finset.sum_singleton]
        · rw [if_neg hi, hχother i hi t, pow_zero]
      · left
        have key : ∀ b c : ℕ, b < c → J' = {b, c} → 52 * 1 + 1 ≤ m := by
          intro b c hbc hJ'bc
          have hcn : c < n := hJ'n c (by rw [hJ'bc]; simp)
          have hn2 : 2 ≤ n := by omega
          obtain ⟨dg, hdg, hdgprop⟩ := exists_digit hs03 hn2 hbc hcn
          set a : Fin Tag.F4.rank → ℕ := fun i => if i = s then 2 ^ b + 2 ^ c else 0 with ha
          have hsum : ∑ i ∈ J', 2 ^ i = 2 ^ b + 2 ^ c := by
            rw [hJ'bc, Finset.sum_pair (ne_of_lt hbc)]
          have hy : ∀ (i : Fin Tag.F4.rank) (t : Kˣ),
              ρ (dC .F4 K i t) y = kpow (k := k) K t ((a i : ℕ) : ℤ) • y := by
            intro i t
            rw [ht.2.2.1 _ (dC_mem_H i t)]
            by_cases hi : i = s
            · subst hi
              simp only [ha, if_pos rfl]
              rw [hχs t, hsum]
              unfold kpow
              rw [zpow_natCast]
            · simp only [ha, if_neg hi]
              rw [hχother i hi t]
              simp [kpow]
          have hE : ∀ b' ∈ ({dg} : Finset ℕ), ∃ e ∈ orbitSpan (ρ.comp (rankOne .F4 K s)) y, e ≠ 0 ∧
              ∀ z : Kˣ, ρ (dC .F4 K s z) e =
                (algebraMap K k (z : K)) ^ (((a s : ℕ) : ℤ) - 2 ^ (b' + 1)) • e := by
            intro b' hb'
            have hb'dg : b' = dg := by simpa using hb'
            subst hb'dg
            have hmem : b' ∈ J' := by
              rw [hJ'bc]
              rcases hdg with rfl | rfl <;> simp
            obtain ⟨e, he, he0, hes⟩ := hwt b' hmem
            refine ⟨e, he, he0, fun z => ?_⟩
            rw [hes z]
            simp only [ha, if_pos rfl]
            rw [hsum]
          have hsep : ∀ (i i' : Fin 12) (j j' : Fin 8) (b' b'' : ℕ), b' ∈ ({dg} : Finset ℕ) →
              b'' ∈ ({dg} : Finset ℕ) →
              (∀ c, ((2 ^ n - 1 : ℕ) : ℤ) ∣
                (((1 : ℤ) • (wF s i • (uF s j • lamF a)) - (2 : ℤ) ^ b' • (wF s i •
                  (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ))) -
                  ((1 : ℤ) • (wF s i' • (uF s j' • lamF a)) - (2 : ℤ) ^ b'' • (wF s i' •
                    (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)))) c) → i = i' ∧ b' = b'' := by
            intro i i' j j' b' b'' hb' hb'' hdiv
            have e1 : b' = dg := by simpa using hb'
            have e2 : b'' = dg := by simpa using hb''
            refine ⟨?_, e1.trans e2.symm⟩
            by_contra hii
            apply hdgprop i i' hii j j'
            intro k0
            have h3 := hdiv k0
            rw [e1, e2] at h3
            simp only [ha, lamF_single, weyl_smul_smulF, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
              one_mul] at h3
            push_cast at h3
            convert h3 using 1
            ring
          have := dim_ge_of_sep hK hρ ht hsJ a hy {dg} hE hsep
          rw [Finset.card_singleton, hfin] at this
          omega
        obtain ⟨x, y', hxy, hJ'eq⟩ := Finset.card_eq_two.1 hc2
        rcases lt_or_gt_of_ne hxy with hlt | hgt
        · exact key x y' hlt hJ'eq
        · exact key y' x hgt (by rw [hJ'eq, Finset.pair_comm])
    · left
      obtain ⟨hu, hΩ, -, -⟩ := family_props s
      have hli : LinearIndependent k (fun j : Fin 8 => ρ (nWC .F4 K (uF s j)) y) :=
        linearIndependent_translates_of_isChevType hρ ht hsJ (v₀ := f4Omega s)
          (reflect_f4Omega s) (fun j : Fin 8 => uF s j) hΩ
      have := copies_finrank_dim hρ ht (s := s) (Dm := 2 ^ J'.card) hdim.ge
        (fun j : Fin 8 => uF s j) hu hli
      rw [hfin] at this
      have h8 : 2 ^ 3 ≤ 2 ^ J'.card := Nat.pow_le_pow_right (by norm_num) hc3
      omega
  · have hs := hex
    obtain ⟨s, hsJ⟩ := hs
    have := dim_ge_of_period hn hK hρ ht hsJ hg hgn h2 hper
    rw [hfin] at this
    left; omega

end TypeBound

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
