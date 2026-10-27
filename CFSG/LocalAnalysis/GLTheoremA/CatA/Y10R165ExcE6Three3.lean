module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (torusRootKernel torusRootKernel_rootDiagUnit
  zetaPow_mem_ker_monomialHom_iff rootCharKernel_zetaPow)
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus)
open CFSG.Open CFSG.RankThree.PartOne.KE6
open CFSG.HardMathSupport.Lang.TwE6Step3
open CFSG.RankThree.Lattice (e6T3W)
open scoped Matrix Pointwise


variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem rootChar_e6T3W_eq_pow [IsAlgClosed Ω] {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {t : ModGL Tag.E6 Ω} (ht : t ∈ twistedTorus (phi3N Ω) Fr) {b : Fin Tag.E6.rank → Ωˣ}
    (hb : t = rootDiagUnit Tag.E6 b) (μ : Fin Tag.E6.rank → ℤ) :
    rootChar b (e6T3W • μ) = rootChar b μ ^ q := by
  have hbT : rootDiagUnit Tag.E6 b ∈ twistedTorus (phi3N Ω) Fr := hb ▸ ht
  have hbker : b ∈ (monomialHom (G := Ωˣ) (phi3Matrix q)ᵀ).ker :=
    (mem_twistedTorus_rootDiagUnit_iff3 (L := Ω) hFr b).1 hbT
  have h1 : rootChar b (phi3Matrix q *ᵥ μ) = 1 :=
    (mem_ker_monomialHom_iff_forall (L := Ω) (phi3Matrix q) b).1 hbker μ
  rw [rootChar_phi3Matrix_mulVec] at h1
  exact mul_inv_eq_one.1 h1

def phi3Torsion (Fr : Ω →+* Ω) (p : ℕ) : Subgroup (ModGL Tag.E6 Ω) where
  carrier := {x | x ∈ twistedTorus (phi3N Ω) Fr ∧ x ^ p = 1}
  mul_mem' := by
    rintro x y ⟨hxT, hxp⟩ ⟨hyT, hyp⟩
    refine ⟨mul_mem hxT hyT, ?_⟩
    have hcomm : x * y = y * x :=
      phi3_torusGroup_comm x (mem_twistedTorus.1 hxT).1 y (mem_twistedTorus.1 hyT).1
    rw [(show Commute x y from hcomm).mul_pow p, hxp, hyp, mul_one]
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' := by
    rintro x ⟨hxT, hxp⟩
    refine ⟨inv_mem hxT, ?_⟩
    rw [inv_pow, hxp, inv_one]

theorem mem_phi3Torsion (Fr : Ω →+* Ω) {p : ℕ} {x : ModGL Tag.E6 Ω} :
    x ∈ phi3Torsion (Ω := Ω) Fr p ↔
      x ∈ twistedTorus (phi3N Ω) Fr ∧ x ^ p = 1 :=
  Iff.rfl

theorem phi3ZetaPow_mem_twistedTorus [IsAlgClosed Ω] {q₀ p : ℕ} [NeZero p] {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ p) (hFr : ∀ c, Fr c = c ^ q₀)
    {z : Fin Tag.E6.rank → ZMod p}
    (hz : (dualMatrix (ZMod p) e6T3W) *ᵥ z = (q₀ : ZMod p) • z) :
    rootDiagUnit Tag.E6 (fun i => ζ ^ (z i).val) ∈ twistedTorus (phi3N Ω) Fr := by
  rw [mem_twistedTorus_rootDiagUnit_iff3 hFr]
  exact (zetaPow_mem_ker_monomialHom_iff hζ ((phi3Matrix q₀)ᵀ) z).2
    ((phi3Matrix_transpose_mulVec_eq_zero_iff q₀ z).2 hz)

noncomputable def phi3TorsionColumn [IsAlgClosed Ω] {q₀ p : ℕ} [NeZero p] {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ p) (hFr : ∀ c, Fr c = c ^ q₀)
    (t : ↥(phi3Torsion (Ω := Ω) Fr p)) : Fin Tag.E6.rank → ZMod p :=
  Classical.choose (exists_column_of_phi3Torus (L := Ω) (Fr := Fr) hFr hζ
    (mem_phi3Torsion Fr |>.1 t.2).1 (mem_phi3Torsion Fr |>.1 t.2).2)

theorem phi3TorsionColumn_spec [IsAlgClosed Ω] {q₀ p : ℕ} [NeZero p] {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ p) (hFr : ∀ c, Fr c = c ^ q₀)
    (t : ↥(phi3Torsion (Ω := Ω) Fr p)) :
    (t : ModGL Tag.E6 Ω) = rootDiagUnit Tag.E6
        (fun i => ζ ^ (phi3TorsionColumn hζ hFr t i).val) ∧
      (dualMatrix (ZMod p) e6T3W) *ᵥ phi3TorsionColumn hζ hFr t =
        (q₀ : ZMod p) • phi3TorsionColumn hζ hFr t := by
  have h := Classical.choose_spec (exists_column_of_phi3Torus (L := Ω) (Fr := Fr) hFr hζ
    (mem_phi3Torsion Fr |>.1 t.2).1 (mem_phi3Torsion Fr |>.1 t.2).2)
  exact ⟨h.1, h.2.1⟩

noncomputable def phi3TorsionEquiv [IsAlgClosed Ω] {q₀ p : ℕ} [NeZero p] {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ p) (hFr : ∀ c, Fr c = c ^ q₀) :
    ↥(phi3Torsion (Ω := Ω) Fr p) ≃
      {z : Fin Tag.E6.rank → ZMod p //
        (dualMatrix (ZMod p) e6T3W) *ᵥ z = (q₀ : ZMod p) • z} where
  toFun t := ⟨phi3TorsionColumn hζ hFr t, (phi3TorsionColumn_spec hζ hFr t).2⟩
  invFun z := by
    refine ⟨rootDiagUnit Tag.E6 (fun i => ζ ^ (z.1 i).val), mem_phi3Torsion Fr |>.2 ⟨?_, ?_⟩⟩
    · exact phi3ZetaPow_mem_twistedTorus hζ hFr z.2
    · change (rootDiagUnitHom Tag.E6 Ω) (fun i => ζ ^ (z.1 i).val) ^ p = 1
      rw [← map_pow]
      have h1 : (fun i => ζ ^ (z.1 i).val) ^ p = 1 := by
        funext i
        rw [Pi.pow_apply, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, Pi.one_apply]
      rw [h1, map_one]
  left_inv t := by
    exact Subtype.ext (phi3TorsionColumn_spec hζ hFr t).1.symm
  right_inv z := by
    have hpow : (rootDiagUnitHom Tag.E6 Ω) (fun i => ζ ^ (z.1 i).val) ^ p = 1 := by
      rw [← map_pow]
      have h1 : (fun i => ζ ^ (z.1 i).val) ^ p = 1 := by
        funext i
        rw [Pi.pow_apply, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, Pi.one_apply]
      rw [h1, map_one]
    let t : ↥(phi3Torsion (Ω := Ω) Fr p) :=
      ⟨rootDiagUnit Tag.E6 (fun i => ζ ^ (z.1 i).val),
        mem_phi3Torsion Fr |>.2 ⟨phi3ZetaPow_mem_twistedTorus hζ hFr z.2, hpow⟩⟩
    have h1 := (phi3TorsionColumn_spec hζ hFr t).1
    have h2 : (fun i => ζ ^ (z.1 i).val) =
        (fun i => ζ ^ (phi3TorsionColumn hζ hFr t i).val) :=
      rootDiagUnit_injective h1
    refine Subtype.ext (funext fun i => ?_)
    have h3 := congrFun h2 i
    exact (ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)).symm

theorem card_phi3Torsion_of_charSpace [IsAlgClosed Ω] {q₀ p : ℕ} [NeZero p] {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ p) (hFr : ∀ c, Fr c = c ^ q₀)
    (hcount : Nat.card {z : Fin Tag.E6.rank → ZMod p //
      (dualMatrix (ZMod p) e6T3W) *ᵥ z = (q₀ : ZMod p) • z} = p ^ 3) :
    Nat.card (phi3Torsion (Ω := Ω) Fr p) = p ^ 3 := by
  rw [Nat.card_congr (phi3TorsionEquiv hζ hFr)]
  exact hcount

def phi3SelX (p q : ℕ) (ζ : Ωˣ) : ModGL Tag.E6 Ω :=
  rootDiagUnit Tag.E6 (fun i => ζ ^ (ExcTwE6.tw6SixZx p q i).val)

def phi3SelZ (p q : ℕ) (ζ : Ωˣ) : ModGL Tag.E6 Ω :=
  rootDiagUnit Tag.E6 (fun i => ζ ^ (ExcTwE6.tw6SixZy p q i).val)

theorem phi3Sel_rootKernel {p : ℕ} [NeZero p] {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (z : Fin Tag.E6.rank → ZMod p) :
    torusRootKernel (rootDiagUnit Tag.E6 (fun i => ζ ^ (z i).val)) = rootKernel z := by
  rw [torusRootKernel_rootDiagUnit, rootCharKernel_zetaPow hζ]

theorem phi3SelX_mem_twistedTorus [IsAlgClosed Ω] {q₀ p q : ℕ} [NeZero p] [Fact p.Prime]
    {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p) (hFr : ∀ c, Fr c = c ^ q₀)
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0)
    (hq₀ : (q₀ : ZMod p) = -(q : ZMod p)) :
    phi3SelX (Ω := Ω) p q ζ ∈ twistedTorus (phi3N Ω) Fr := by
  refine phi3ZetaPow_mem_twistedTorus hζ hFr ?_
  have h := ExcTwE6.tw6SixZx_mulVec p q hq
  rwa [hq₀]

theorem phi3SelX_isA2A2 [IsAlgClosed Ω] {p q : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    IsA2A2Kernel (torusRootKernel (phi3SelX (Ω := Ω) p q ζ)) := by
  change IsA2A2Kernel (torusRootKernel
    (rootDiagUnit Tag.E6 (fun i => ζ ^ (ExcTwE6.tw6SixZx p q i).val)))
  rw [phi3Sel_rootKernel hζ]
  exact ExcTwE6.tw6SixZx_isA2A2Kernel hp5 hq

theorem phi3SelX_supportA2_subset [IsAlgClosed Ω] {p q : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    parabolicRoots Tag.E6 ExcTwE6.tw6SixSupportA2 ⊆
      torusRootKernel (phi3SelX (Ω := Ω) p q ζ) := by
  change parabolicRoots Tag.E6 ExcTwE6.tw6SixSupportA2 ⊆
    torusRootKernel (rootDiagUnit Tag.E6
      (fun i => ζ ^ (ExcTwE6.tw6SixZx p q i).val))
  rw [phi3Sel_rootKernel hζ]
  exact ExcTwE6.tw6SixSupportA2_subset_rootKernel_zx hp5 hq

theorem phi3SelZ_supportA2_subset [IsAlgClosed Ω] {p q : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    parabolicRoots Tag.E6 ExcTwE6.tw6SixSupportA2 ⊆
      torusRootKernel (phi3SelZ (Ω := Ω) p q ζ) := by
  change parabolicRoots Tag.E6 ExcTwE6.tw6SixSupportA2 ⊆
    torusRootKernel (rootDiagUnit Tag.E6
      (fun i => ζ ^ (ExcTwE6.tw6SixZy p q i).val))
  rw [phi3Sel_rootKernel hζ]
  exact ExcTwE6.tw6SixSupportA2_subset_rootKernel_zy hp5 hq

theorem phi3SelZ_notMem_zpowers [IsAlgClosed Ω] {p q : ℕ} [Fact p.Prime] {ζ : Ωˣ}
    (hζ : IsPrimitiveRoot ζ p) :
    phi3SelZ (Ω := Ω) p q ζ ∉ Subgroup.zpowers (phi3SelX (Ω := Ω) p q ζ) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  intro hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h1 : (fun i => ζ ^ (ExcTwE6.tw6SixZy p q i).val) =
      (fun i => (ζ ^ (ExcTwE6.tw6SixZx p q i).val) ^ m) := by
    apply rootDiagUnit_injective
    have h2 : (rootDiagUnitHom Tag.E6 Ω)
        (fun i => ζ ^ (ExcTwE6.tw6SixZy p q i).val) =
        ((rootDiagUnitHom Tag.E6 Ω)
          (fun i => ζ ^ (ExcTwE6.tw6SixZx p q i).val)) ^ m := by
      change phi3SelZ (Ω := Ω) p q ζ = (phi3SelX (Ω := Ω) p q ζ) ^ m
      exact hm.symm
    rw [← map_zpow] at h2
    exact h2
  have h4 : ζ ^ (m : ℤ) = 1 := by
    have h := congrFun h1 (e6Index 4)
    have h' : (1 : Ωˣ) = (ζ ^ ((1 : ZMod p).val)) ^ m := by
      simpa [ExcTwE6.tw6SixZx,
        ExcTwE6.tw6SixZy, e6Index] using h
    rw [ZMod.val_one p, pow_one] at h'
    exact h'.symm
  have h5 : ζ = 1 := by
    have h := congrFun h1 (e6Index 5)
    have h' : ζ ^ ((1 : ZMod p).val) = 1 := by
      simpa [ExcTwE6.tw6SixZx,
        ExcTwE6.tw6SixZy, e6Index] using h
    rwa [ZMod.val_one p, pow_one] at h'
  exact hζ.ne_one (by have := (Fact.out : p.Prime).one_lt; omega) h5

theorem exists_second_point_of_A2A2 [IsAlgClosed Ω] {q₀ p q : ℕ} [Fact p.Prime]
    (hp5 : 5 < p) (hFr : ∀ c, Fr c = c ^ q₀)
    (hq₀ : (q₀ : ZMod p) ^ 2 + (q₀ : ZMod p) + 1 = 0)
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0)
    (hq' : (q₀ : ZMod p) = -(q : ZMod p))
    (hcount : Nat.card {z : Fin Tag.E6.rank → ZMod p //
      (dualMatrix (ZMod p) e6T3W) *ᵥ z = (q₀ : ZMod p) • z} = p ^ 3)
    {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    {A : Subgroup (ModGL Tag.E6 Ω)} (hA : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hAT : A ≤ twistedTorus (phi3N Ω) Fr) :
    ∃ x ∈ A, ∃ z ∈ A, z ∉ Subgroup.zpowers x ∧
      IsA2A2Kernel (torusRootKernel x) ∧
      parabolicRoots Tag.E6 ExcTwE6.tw6SixSupportA2 ⊆
        torusRootKernel x ∧
      parabolicRoots Tag.E6 ExcTwE6.tw6SixSupportA2 ⊆
        torusRootKernel z := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hT0card : Nat.card (phi3Torsion (Ω := Ω) Fr p) = p ^ 3 :=
    card_phi3Torsion_of_charSpace hζ hFr hcount
  have hAle : A ≤ phi3Torsion (Ω := Ω) Fr p := fun x hx => ⟨hAT hx, hA.2 x hx⟩
  haveI : Finite (phi3Torsion (Ω := Ω) Fr p) :=
    Nat.finite_of_card_ne_zero (by rw [hT0card]; positivity)
  have hAeq : A = phi3Torsion (Ω := Ω) Fr p :=
    Subgroup.eq_of_le_of_card_ge hAle (by rw [hT0card, hAcard])
  have hx0T : phi3SelX (Ω := Ω) p q ζ ∈ phi3Torsion (Ω := Ω) Fr p := by
    refine (mem_phi3Torsion Fr).2 ⟨phi3SelX_mem_twistedTorus hζ hFr hq hq', ?_⟩
    change (rootDiagUnitHom Tag.E6 Ω)
      (fun i => ζ ^ (ExcTwE6.tw6SixZx p q i).val) ^ p = 1
    rw [← map_pow]
    have h1 : (fun i => ζ ^ (ExcTwE6.tw6SixZx p q i).val) ^ p = 1 := by
      funext i
      rw [Pi.pow_apply, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, Pi.one_apply]
    rw [h1, map_one]
  have hz0T : phi3SelZ (Ω := Ω) p q ζ ∈ phi3Torsion (Ω := Ω) Fr p := by
    refine (mem_phi3Torsion Fr).2 ⟨?_, ?_⟩
    · refine phi3ZetaPow_mem_twistedTorus hζ hFr ?_
      have h := ExcTwE6.tw6SixZy_mulVec p q hq
      rwa [hq']
    · change (rootDiagUnitHom Tag.E6 Ω)
        (fun i => ζ ^ (ExcTwE6.tw6SixZy p q i).val) ^ p = 1
      rw [← map_pow]
      have h1 : (fun i => ζ ^ (ExcTwE6.tw6SixZy p q i).val) ^ p = 1 := by
        funext i
        rw [Pi.pow_apply, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, Pi.one_apply]
      rw [h1, map_one]
  refine ⟨phi3SelX (Ω := Ω) p q ζ, hAeq ▸ hx0T, phi3SelZ (Ω := Ω) p q ζ,
    hAeq ▸ hz0T, phi3SelZ_notMem_zpowers hζ, phi3SelX_isA2A2 hp5 hζ hq,
    phi3SelX_supportA2_subset hp5 hζ hq, phi3SelZ_supportA2_subset hp5 hζ hq⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
