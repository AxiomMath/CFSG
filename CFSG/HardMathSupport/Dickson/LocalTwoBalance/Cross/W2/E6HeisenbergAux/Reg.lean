module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.RegAux
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Chevalley.LangRootRankOneTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.ComponentClassification.Burgoyne.E2 (regCoweight
  toralCentralizer_eq_torusGroup_of_regular)
open CFSG.ComponentClassification.CatLeafProof (eq_of_torusRootChar_single
  torusRootChar_rootDiagUnit rootChar_single')
open CFSG.LieType.Steinberg.Adjoint (iform iform_smul_right)

section Lattice


theorem corootPair_finset_sum {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {ι : Type*}
    (s : Finset ι) (c : ι → ℤ) (u : ι → Fin τ.rank → ℤ) :
    corootPair β (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i * corootPair β (u i) := by
  have hp := iform_self_pos_of_isRoot hβ
  have h1 := corootPair_mul hβ (∑ i ∈ s, c i • u i)
  have h2 : (∑ i ∈ s, c i * corootPair β (u i)) * iform β β =
      2 * iform β (∑ i ∈ s, c i • u i) := by
    rw [iform_finset_sum_right, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iform_smul_right, mul_assoc, corootPair_mul hβ]
    ring
  exact mul_right_cancel₀ hp.ne' (h1.trans h2.symm)

theorem corootPair_eq_sum_single' {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (v : Fin τ.rank → ℤ) : corootPair β v = ∑ j, v j * corootPair β (Pi.single j 1) := by
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  exact corootPair_finset_sum hβ _ _ _

theorem corootPair_smul_smul' {τ : Tag} (w : WeylGroup τ) (δ v : Fin τ.rank → ℤ) :
    corootPair (w • δ) (w • v) = corootPair δ v := by
  simp only [corootPair, iform_smul]

theorem sum_regCoweight_mul {τ : Tag} (Γ : List ((Fin τ.rank → ℤ) × ℤ))
    (hΓ : ∀ y ∈ Γ, IsRoot τ y.1) (v : Fin τ.rank → ℤ) :
    ∑ j, regCoweight Γ j * v j = (Γ.map fun y => y.2 * corootPair y.1 v).sum := by
  induction Γ with
  | nil => simp [regCoweight]
  | cons y Γ ih =>
    have hy := hΓ y List.mem_cons_self
    have ih' := ih fun y' hy' => hΓ y' (List.mem_cons_of_mem y hy')
    simp only [regCoweight, List.map_cons, List.sum_cons] at ih' ⊢
    rw [← ih', corootPair_eq_sum_single' hy v, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem sum_regCoweight_map_smul {τ : Tag} (t : WeylGroup τ) (Γ : List ((Fin τ.rank → ℤ) × ℤ))
    (hΓ : ∀ y ∈ Γ, IsRoot τ y.1) (v : Fin τ.rank → ℤ) :
    ∑ j, regCoweight (Γ.map fun y => (t • y.1, y.2)) j * v j =
      ∑ j, regCoweight Γ j * (t⁻¹ • v) j := by
  have hΓt : ∀ y ∈ Γ.map (fun y => (t • y.1, y.2)), IsRoot τ y.1 := by
    intro y hy
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
    exact IsRoot.smul (hΓ y' hy') t
  rw [sum_regCoweight_mul _ hΓt, sum_regCoweight_mul Γ hΓ, List.map_map]
  congr 1
  refine List.map_congr_left fun y _ => ?_
  simp only [Function.comp_apply]
  rw [← corootPair_smul_smul' t⁻¹ (t • y.1) v, inv_smul_smul]

end Lattice

section Torus


variable {τ : Tag} {M : Type} [Field M]

theorem torusRootChar_rootTorusSL2' {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : Mˣ)
    (j : Fin τ.rank) :
    torusRootChar (rootTorusSL2 τ M β c) (Pi.single j 1) =
      ((c ^ corootPair β (Pi.single j 1) : Mˣ) : M) := by
  obtain ⟨-, -, -, -, h5, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ M hβ
  exact torusRootChar_eq_of_apply (isRoot_single τ j) ((h5 c).2 _ (isRoot_single τ j))

theorem exists_commute_rootTorus_prod' {x : ModGL τ M} (ζ : Mˣ)
    (Γ : List ((Fin τ.rank → ℤ) × ℤ)) (hΓ : ∀ y ∈ Γ, IsRoot τ y.1)
    (h : ∀ y ∈ Γ, ∀ s : Mˣ, Commute x (rootTorusSL2 τ M y.1 s)) :
    ∃ P ∈ torusGroup τ M, Commute x P ∧ ∀ j : Fin τ.rank,
      torusRootChar P (Pi.single j 1) = ((ζ ^ regCoweight Γ j : Mˣ) : M) := by
  induction Γ with
  | nil =>
    refine ⟨1, one_mem _, Commute.one_right x, fun j => ?_⟩
    rw [torusRootChar_one]
    simp [regCoweight]
  | cons y Γ ih =>
    obtain ⟨P, hPT, hxP, hPχ⟩ := ih (fun y' hy' => hΓ y' (List.mem_cons_of_mem y hy'))
      fun y' hy' => h y' (List.mem_cons_of_mem y hy')
    have hy := hΓ y List.mem_cons_self
    obtain ⟨-, hQT, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ M hy
    refine ⟨rootTorusSL2 τ M y.1 (ζ ^ y.2) * P, mul_mem (hQT _) hPT,
      (h y List.mem_cons_self _).mul_right hxP, fun j => ?_⟩
    rw [torusRootChar_mul (torusGroup_le_diagonalGroup (hQT _))
      (torusGroup_le_diagonalGroup hPT), hPχ j, torusRootChar_rootTorusSL2' hy]
    simp only [regCoweight, List.map_cons, List.sum_cons, zpow_add, ← zpow_mul, Units.val_mul]

theorem commute_rootTorusSL2_of_commute {x : ModGL τ M} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hp : ∀ c : M, Commute x (pinnedX τ M β c)) (hn : ∀ c : M, Commute x (pinnedX τ M (-β) c))
    (s : Mˣ) : Commute x (rootTorusSL2 τ M β s) := by
  obtain ⟨hL, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ M hβ
  have hle : rootRankOneGroup τ M β ≤ Subgroup.centralizer {x} := by
    rw [hL]
    refine sup_le ?_ ?_ <;> rw [rootSubgroup, Subgroup.closure_le] <;> rintro _ ⟨c, rfl⟩ <;>
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    · exact (hp c).eq.symm
    · exact (hn c).eq.symm
  have hmem : rootTorusSL2 τ M β s ∈ rootRankOneGroup τ M β := ⟨HSL s, rfl⟩
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hmem)).symm

end Torus

theorem regular_witness {L : Type} [Field L] [IsAlgClosed L]
    (b : Fin Tag.E6.rank → ZMod 3) {w : WeylGroup Tag.E6} (hw : w ∈ charStabilizer (triChar b))
    (hsh : triPairing b (e6Shift w) ≠ 0) :
    ∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : 7 < ℓ) (ζ : Lˣ) (_ : orderOf ζ = ℓ) (z : Fin Tag.E6.rank → ℤ),
      (∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ¬ (ℓ : ℤ) ∣ ∑ j, z j * α j) ∧
      ∀ y : ModGL Tag.E6 L,
        (∀ β ∈ kernelRoots (triChar b), ∀ c : L, Commute y (pinnedX Tag.E6 L β c)) →
          Commute y (rootDiagUnit Tag.E6 (fun j => ζ ^ z j)) := by
  obtain ⟨t, b', hb', htb, -, -⟩ := exists_rep b hw hsh
  obtain ⟨Γ', hΓ'mem, hΓ'reg⟩ := exists_regFam hb'
  have hΓ' : ∀ y ∈ Γ', IsRoot Tag.E6 y.1 := fun y hy => (hΓ'mem y hy).1
  set Γ : List ((Fin Tag.E6.rank → ℤ) × ℤ) := Γ'.map fun y => (t • y.1, y.2) with hΓdef
  have hΓroot : ∀ y ∈ Γ, IsRoot Tag.E6 y.1 := by
    intro y hy
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
    exact IsRoot.smul (hΓ' y' hy') t
  have hΓker : ∀ y ∈ Γ, y.1 ∈ kernelRoots (triChar b) ∧ -y.1 ∈ kernelRoots (triChar b) := by
    intro y hy
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
    have h0 : triPairing b (t • y'.1) = 0 := by rw [htb]; exact (hΓ'mem y' hy').2
    have h1 : triPairing b (-(t • y'.1)) = 0 := by
      have h2 := triPairing_add b (t • y'.1) (-(t • y'.1))
      rw [add_neg_cancel, triPairing_zero, h0, zero_add] at h2
      exact h2.symm
    exact ⟨mem_kernelRoots_triChar.2 ⟨IsRoot.smul (hΓ' y' hy') t, h0⟩,
      mem_kernelRoots_triChar.2 ⟨IsRoot.neg (IsRoot.smul (hΓ' y' hy') t), h1⟩⟩
  have hreg : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      (∑ j, regCoweight Γ j * α j) ≠ 0 ∧ (∑ j, regCoweight Γ j * α j).natAbs < 12 := by
    intro α hα
    rw [hΓdef, sum_regCoweight_map_smul t Γ' hΓ' α]
    exact hΓ'reg _ (IsRoot.smul hα t⁻¹)
  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (12 + ringChar L + 8)
  have hℓ7 : 7 < ℓ := by omega
  have hℓL : (ℓ : L) ≠ 0 := by
    intro h0
    rcases hℓ.eq_one_or_self_of_dvd _ (ringChar.dvd h0) with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · omega
  have : NeZero (ℓ : L) := ⟨hℓL⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L ℓ
  set ζ : Lˣ := (hζ₀.isUnit hℓ.ne_zero).unit
  have hζ : orderOf ζ = ℓ := (IsPrimitiveRoot.coe_units_iff.1 hζ₀).eq_orderOf.symm
  refine ⟨ℓ, hℓ, hℓ7, ζ, hζ, regCoweight Γ, fun α hα hdvd => ?_, fun y hy => ?_⟩
  · obtain ⟨hne, hlt⟩ := hreg α hα
    have h1 : ℓ ∣ (∑ j, regCoweight Γ j * α j).natAbs := Int.natCast_dvd.1 hdvd
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hne) h1
    omega
  ·
    have hcomm : ∀ x ∈ Γ, ∀ s : Lˣ, Commute y (rootTorusSL2 Tag.E6 L x.1 s) := fun x hx s =>
      commute_rootTorusSL2_of_commute (hΓroot x hx) (hy _ (hΓker x hx).1)
        (hy _ (hΓker x hx).2) s
    obtain ⟨P, hPT, hyP, hPχ⟩ := exists_commute_rootTorus_prod' ζ Γ hΓroot hcomm
    have hdz : rootDiagUnit Tag.E6 (fun j => ζ ^ regCoweight Γ j) ∈ torusGroup Tag.E6 L := by
      obtain ⟨-, t', ht'⟩ :=
        exceptional_Lang_adjoint_diagonal_lift Tag.E6 L (fun j => ζ ^ regCoweight Γ j)
      rw [ht']
      refine Subgroup.list_prod_mem _ fun q hq => ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hq
      exact torusElt_mem_torusGroup j _
    have hPeq : P = rootDiagUnit Tag.E6 (fun j => ζ ^ regCoweight Γ j) :=
      eq_of_torusRootChar_single hPT hdz fun j => by
        rw [hPχ j, torusRootChar_rootDiagUnit _ (isRoot_single Tag.E6 j), rootChar_single']
    rw [← hPeq]
    exact hyP

theorem mem_torusGroup_of_commute_kernelRoots
    {L : Type} [Field L] [IsAlgClosed L]
    (b : Fin Tag.E6.rank → ZMod 3) {w : WeylGroup Tag.E6} (hw : w ∈ charStabilizer (triChar b))
    (hsh : triPairing b (e6Shift w) ≠ 0) {z : ModGL Tag.E6 L} (hz : z ∈ adjointGroup Tag.E6 L)
    (hc : ∀ β ∈ kernelRoots (triChar b), ∀ c : L, Commute z (pinnedX Tag.E6 L β c)) :
    z ∈ torusGroup Tag.E6 L := by
  obtain ⟨ℓ, hℓ, hℓ7, ζ, hζ, z', hreg, hcomm⟩ := regular_witness (L := L) b hw hsh
  rw [← toralCentralizer_eq_torusGroup_of_regular (τ := Tag.E6) (Or.inl rfl) hℓ hℓ7 hζ z' hreg]
  exact Subgroup.mem_inf.2 ⟨hz, Subgroup.mem_centralizer_singleton_iff.2 (hcomm z hc).eq⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
