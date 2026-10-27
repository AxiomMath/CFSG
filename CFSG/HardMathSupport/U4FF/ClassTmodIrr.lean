module

public import CFSG.HardMathSupport.U4FF.ClassTmodNorm
public import CFSG.Quasithin.Background.SmithCurtisBasic

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.QuasithinUnique.Setup.X7


section Irr

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {k : Type} [Field k] [CharP k 2]
  [Algebra K k]

@[expose] noncomputable def Tmod (K : Type) [Field K] [Finite K] [CharP K 2] {n : ℕ} (l : Lbl n)
    (k : Type) [Field k] [CharP k 2] [Algebra K k] : SU4 K n →* Matrix (TIdx l) (TIdx l) k :=
  TmodΦ l (fun i => frobTw K k i)

@[expose] noncomputable def Trep (K : Type) [Field K] [Finite K] [CharP K 2] {n : ℕ} (l : Lbl n)
    (k : Type) [Field k] [CharP k 2] [Algebra K k] :
    Representation k (SU4 K n) (TIdx l → k) :=
  (Matrix.toLinAlgEquiv' (R := k) (n := TIdx l)).toAlgHom.toMonoidHom.comp (Tmod K l k)

theorem Trep_apply (l : Lbl n) (g : SU4 K n) (w : TIdx l → k) :
    Trep K l k g w = Tmod K l k g *ᵥ w := by
  simp [Trep, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

theorem Tmod_eq (l : Lbl n) : Tmod K l k = TmodΦ l (fun i => frobTw K k i) := rfl

theorem isPGroup_LowerU : IsPGroup 2 ↥(LowerU K n) := by
  intro g
  refine ⟨2, ?_⟩
  have h4 := isLowerUni_pow_four (mem_LowerU.mp g.2)
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simpa [Units.val_pow_eq_pow_val] using h4

theorem isPGroup_UpperU : IsPGroup 2 ↥(UpperU K n) := by
  intro g
  refine ⟨2, ?_⟩
  have h4 := isUpperUni_pow_four (mem_UpperU.mp g.2)
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simpa [Units.val_pow_eq_pow_val] using h4

theorem steinberg_regular (hK : Nat.card K = (2 ^ n) ^ 2) :
    Submodule.span k (Set.range fun u : ↥(LowerU K n) =>
        Trep K (rhoL n) k (u : SU4 K n) (hwv (rhoL n) k)) = ⊤ ∧
      Module.finrank k ↥(fixedSub ((Trep K (rhoL n) k).comp (LowerU K n).subtype) ⊤) = 1 := by
  classical
  haveI : Fintype ↥(LowerU K n) := Fintype.ofFinite _
  have hdim : Module.finrank k (TIdx (rhoL n) → k) = Fintype.card ↥(LowerU K n) := by
    have h2 : Fintype.card ↥(LowerU K n) = (2 ^ n) ^ 6 := by
      rw [← Nat.card_eq_fintype_card, card_LowerU hK]
    rw [Module.finrank_fintype_fun_eq_card, h2, Fintype.card_pi]
    simp only [Fintype.card_fin]
    show (∏ _x : Fin n, (64 : ℕ)) = (2 ^ n) ^ 6
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hnorm : ∑ g : ↥(LowerU K n),
      ((Trep K (rhoL n) k).comp (LowerU K n).subtype) g (hwv (rhoL n) k) ≠ 0 := by
    have h := norm_hwv_ne_zero (n := n) (k := k) hK
    have e : ∑ g : ↥(LowerU K n),
        ((Trep K (rhoL n) k).comp (LowerU K n).subtype) g (hwv (rhoL n) k) =
        ∑ u : ↥(LowerU K n), TmodΦ (rhoL n) (fun i => frobTw K k i) (u : SU4 K n) *ᵥ
          hwv (rhoL n) k := Finset.sum_congr rfl fun g _ => Trep_apply _ _ _
    rw [e]
    exact h
  obtain ⟨b, hb1, -, hb3⟩ := orbit_regular_of_norm_ne_zero k Nat.prime_two isPGroup_LowerU
    ((Trep K (rhoL n) k).comp (LowerU K n).subtype) (hwv (rhoL n) k) hnorm hdim
  refine ⟨?_, hb3⟩
  have hr : Set.range b = Set.range fun u : ↥(LowerU K n) =>
      Trep K (rhoL n) k (u : SU4 K n) (hwv (rhoL n) k) := by
    congr 1
    funext u
    exact hb1 u
  rw [← hr]
  exact b.span_eq

theorem span_orbit_eq_top (hK : Nat.card K = (2 ^ n) ^ 2) (l : Lbl n) :
    Submodule.span k (Set.range fun u : ↥(LowerU K n) =>
        Trep K l k (u : SU4 K n) (hwv l k)) = ⊤ := by
  obtain ⟨hspan, -⟩ := steinberg_regular hK (k := k)
  have hmap : ∀ u : ↥(LowerU K n), Trep K l k (u : SU4 K n) (hwv l k) =
      PiTot l k *ᵥ Trep K (rhoL n) k (u : SU4 K n) (hwv (rhoL n) k) := by
    intro u
    rw [Trep_apply, Trep_apply, Matrix.mulVec_mulVec, Tmod_eq, Tmod_eq,
      PiTot_equiv hK l (fun i => frobTw K k i) u.2, ← Matrix.mulVec_mulVec, PiTot_hwv]
  have hrange : Set.range (fun u : ↥(LowerU K n) => Trep K l k (u : SU4 K n) (hwv l k)) =
      (Matrix.mulVecLin (PiTot l k)) '' Set.range (fun u : ↥(LowerU K n) =>
        Trep K (rhoL n) k (u : SU4 K n) (hwv (rhoL n) k)) := by
    rw [← Set.range_comp]
    congr 1
    funext u
    exact hmap u
  rw [hrange, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]
  intro w
  exact ⟨PirTot l k *ᵥ w, by
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, PiTot_mul_PirTot, Matrix.one_mulVec]⟩

theorem fixed_line (hK : Nat.card K = (2 ^ n) ^ 2) (l : Lbl n) :
    ∃ v ∈ fixedSub (Trep K l k) (LowerU K n), ∀ w ∈ fixedSub (Trep K l k) (LowerU K n),
      ∃ c : k, w = c • v := by
  obtain ⟨-, hfin⟩ := steinberg_regular hK (k := k)
  set Fρ := fixedSub (Trep K (rhoL n) k) (LowerU K n) with hFρdef
  set Fl := fixedSub (Trep K l k) (LowerU K n) with hFldef
  have hFρ : Module.finrank k Fρ = 1 := by
    have e : fixedSub ((Trep K (rhoL n) k).comp (LowerU K n).subtype) ⊤ = Fρ := by
      ext w
      constructor
      · intro h g hg
        exact h ⟨g, hg⟩ (Subgroup.mem_top _)
      · intro h g _
        exact h g g.2
    rw [← e]
    exact hfin
  have hmem : ∀ w ∈ Fl, IotaTot l k *ᵥ w ∈ Fρ := by
    intro w hw u hu
    have hw' := hw u hu
    rw [Trep_apply] at hw' ⊢
    rw [Matrix.mulVec_mulVec, Tmod_eq, ← IotaTot_equiv hK l (fun i => frobTw K k i) hu,
      ← Matrix.mulVec_mulVec]
    rw [Tmod_eq] at hw'
    rw [hw']
  let f : Fl →ₗ[k] Fρ := (Matrix.mulVecLin (IotaTot l k)).restrict hmem
  have hinj : Function.Injective f := by
    intro w w' h
    have h1 : IotaTot l k *ᵥ (w : TIdx l → k) = IotaTot l k *ᵥ (w' : TIdx l → k) :=
      congrArg Subtype.val h
    have h2 : (w : TIdx l → k) = (w' : TIdx l → k) := by
      calc (w : TIdx l → k) = (IolTot l k * IotaTot l k) *ᵥ (w : TIdx l → k) := by
            rw [IolTot_mul_IotaTot, Matrix.one_mulVec]
        _ = IolTot l k *ᵥ (IotaTot l k *ᵥ (w : TIdx l → k)) := by rw [Matrix.mulVec_mulVec]
        _ = IolTot l k *ᵥ (IotaTot l k *ᵥ (w' : TIdx l → k)) := by rw [h1]
        _ = (IolTot l k * IotaTot l k) *ᵥ (w' : TIdx l → k) := by rw [Matrix.mulVec_mulVec]
        _ = (w' : TIdx l → k) := by rw [IolTot_mul_IotaTot, Matrix.one_mulVec]
    exact Subtype.ext h2
  have hle : Module.finrank k Fl ≤ 1 := by
    have := LinearMap.finrank_le_finrank_of_injective hinj
    omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hle
  refine ⟨v, v.2, fun w hw => ?_⟩
  obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem Tmod_fixed_and_irreducible (hK : Nat.card K = (2 ^ n) ^ 2) (l : Lbl n) :
    fixedSub (Trep K l k) (UpperU K n) = Submodule.span k {hwv l k} ∧
      (Trep K l k).IsIrreducible := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : hwv l k ∈ fixedSub (Trep K l k) (UpperU K n) := by
    intro u hu
    rw [Trep_apply, Tmod_eq]
    exact TmodΦ_upper_fix hK l _ hu
  exact fixedSub_eq_span_and_irreducible k Nat.prime_two (Trep K l k) (LowerU K n) (UpperU K n)
    isPGroup_UpperU (jSU K n) (fun u hu => conj_mem_UpperU_of_mem_LowerU hu) (hwv l k)
    (hwv_ne_zero l) hv (span_orbit_eq_top hK l) (fixed_line hK l)

theorem Tmod_irreducible (hK : Nat.card K = (2 ^ n) ^ 2) (l : Lbl n) :
    (Trep K l k).IsIrreducible :=
  (Tmod_fixed_and_irreducible hK l).2

theorem Tmod_isSimpleRep (hK : Nat.card K = (2 ^ n) ^ 2) (l : Lbl n) :
    CFSG.Quasithin.SmithCurtis.IsSimpleRep (Trep K l k) :=
  (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp (Tmod_irreducible hK l)

end Irr

end CFSG.HardMathSupport.U4FF
