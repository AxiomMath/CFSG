module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltNatTwist
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NatFF

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct_mk)
open CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive (natFF mem_altFix_iff_altAct)

variable {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)} {M : Subgroup V} {n : ℕ}

theorem exists_altNatHom (D : AltNatModule L M n) (hodd : Odd n) (h7 : 7 ≤ n)
    (hαinj : Function.Injective D.α) {A : Subgroup (MulAut V)}
    (hAN : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (hAM : ∀ a ∈ A, ∀ m ∈ M, a m ∈ M) :
    ∃ S : ↥A →* Perm (Fin n),
      (∀ (a : ↥A) (m m' : ↥M), (m' : V) = (a : MulAut V) (m : V) →
        Multiplicative.toAdd (D.e m') = evenWeightPerm (S a) (Multiplicative.toAdd (D.e m))) ∧
      (∀ (a : ↥A) (l l' : ↥L), (l' : MulAut V) = (a : MulAut V) * l * (a : MulAut V)⁻¹ →
        (D.α l' : Perm (Fin n)) = S a * (D.α l : Perm (Fin n)) * (S a)⁻¹) := by
  have hnorm : ∀ a : ↥A, ∀ l ∈ L, (a : MulAut V) * l * (a : MulAut V)⁻¹ ∈ L ∧
      (a : MulAut V)⁻¹ * l * (a : MulAut V) ∈ L := fun a l hl =>
    ⟨hAN a a.2 l hl, by simpa using hAN (a : MulAut V)⁻¹ (A.inv_mem a.2) l hl⟩
  have hex : ∀ a : ↥A, ∃ σ : Perm (Fin n),
      (∀ m : ↥M, Multiplicative.toAdd (D.e ⟨(a : MulAut V) (m : V), hAM a a.2 m m.2⟩) =
        evenWeightPerm σ (Multiplicative.toAdd (D.e m))) ∧
      ∀ l : ↥L, (D.α ⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, (hnorm a l l.2).1⟩ : Perm (Fin n)) =
        σ * (D.α l : Perm (Fin n)) * σ⁻¹ :=
    fun a => exists_altNatTwist D hodd h7 hαinj (hnorm a) (hAM a a.2)
  choose σ hσ1 hσ2 using hex
  let S : ↥A →* Perm (Fin n) := MonoidHom.mk' σ (fun a b => by
    refine altNat_perm_unique hodd fun x => ?_
    set m : ↥M := D.e.symm (Multiplicative.ofAdd x) with hm
    have hx : Multiplicative.toAdd (D.e m) = x := by rw [hm, MulEquiv.apply_symm_apply]; rfl
    have hbm : ((b : MulAut V) (m : V)) ∈ M := hAM b b.2 m m.2
    have hab : (((a * b : ↥A) : MulAut V) (m : V)) ∈ M := hAM (a * b) (a * b).2 m m.2
    calc evenWeightPerm (σ (a * b)) x
        = evenWeightPerm (σ (a * b)) (Multiplicative.toAdd (D.e m)) := by rw [hx]
      _ = Multiplicative.toAdd (D.e ⟨((a * b : ↥A) : MulAut V) (m : V), hab⟩) :=
          (hσ1 (a * b) m).symm
      _ = Multiplicative.toAdd (D.e ⟨(a : MulAut V) ((⟨(b : MulAut V) (m : V), hbm⟩ : ↥M) : V),
            hAM a a.2 _ hbm⟩) := rfl
      _ = evenWeightPerm (σ a) (Multiplicative.toAdd (D.e ⟨(b : MulAut V) (m : V), hbm⟩)) :=
          hσ1 a ⟨(b : MulAut V) (m : V), hbm⟩
      _ = evenWeightPerm (σ a) (evenWeightPerm (σ b) (Multiplicative.toAdd (D.e m))) := by
          rw [← hσ1 b m]
      _ = evenWeightPerm (σ a * σ b) x := by rw [← altNat_evenWeightPerm_mul, hx])
  refine ⟨S, ?_, ?_⟩
  · intro a m m' h
    have : m' = ⟨(a : MulAut V) (m : V), hAM a a.2 m m.2⟩ := Subtype.ext h
    rw [this]
    exact hσ1 a m
  · intro a l l' h
    have : l' = ⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, (hnorm a l l.2).1⟩ := Subtype.ext h
    rw [this]
    exact hσ2 a l

section Count

variable [Finite V]

theorem altNat_tight (D : AltNatModule L M n) (hodd : Odd n) (h7 : 7 ≤ n)
    (hαinj : Function.Injective D.α) {A : Subgroup (MulAut V)} {W : Subgroup V}
    (hAN : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (hAM : ∀ a ∈ A, ∀ m ∈ M, a m ∈ M)
    (hMW : M ≤ W) (hA2 : ∀ a ∈ A, a * a = 1)
    (hcent : ∀ a ∈ A, (∀ l ∈ L, a * l = l * a) → ∀ w ∈ W, a w = w) :
    Nat.card A * Nat.card ↥(W ⊓ fixV A) ≤ Nat.card ↥(A ⊓ centSub W) * Nat.card W := by
  classical
  obtain ⟨S, hS1, hS2⟩ := exists_altNatHom D hodd h7 hαinj hAN hAM
  have hkerS : ∀ a : ↥A, S a = 1 ↔ (a : MulAut V) ∈ centSub W := by
    intro a
    constructor
    · intro h1
      have hcomm : ∀ l ∈ L, (a : MulAut V) * l = l * (a : MulAut V) := by
        intro l hl
        have h2 := hS2 a ⟨l, hl⟩ ⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, hAN a a.2 l hl⟩ rfl
        rw [h1] at h2
        simp only [one_mul, inv_one, mul_one] at h2
        have h3 : (⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, hAN a a.2 l hl⟩ : ↥L) = ⟨l, hl⟩ :=
          hαinj (Subtype.ext h2)
        have h4 : (a : MulAut V) * l * (a : MulAut V)⁻¹ = l := congrArg Subtype.val h3
        calc (a : MulAut V) * l = ((a : MulAut V) * l * (a : MulAut V)⁻¹) * (a : MulAut V) := by
              group
          _ = l * (a : MulAut V) := by rw [h4]
      exact fun w hw => hcent a a.2 hcomm w hw
    · intro hW
      refine eq_one_of_evenWeightPerm_eq_self hodd fun x => ?_
      set m : ↥M := D.e.symm (Multiplicative.ofAdd x) with hm
      have hx : Multiplicative.toAdd (D.e m) = x := by
        rw [hm, MulEquiv.apply_symm_apply]; rfl
      have hfix : (a : MulAut V) (m : V) = (m : V) := hW (m : V) (hMW m.2)
      have h1 := hS1 a m m hfix.symm
      rw [hx] at h1
      exact h1.symm
  have hkerEq : S.ker = (A ⊓ centSub W).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨a.2, (hkerS a).1 h⟩, fun h => (hkerS a).2 h.2⟩
  have hcardA : Nat.card A = Nat.card ↥(A ⊓ centSub W) * Nat.card S.range := by
    have h1 := Subgroup.card_mul_index S.ker
    rw [Subgroup.index_ker, hkerEq] at h1
    have h2 : Nat.card ↥((A ⊓ centSub W).subgroupOf A) = Nat.card ↥(A ⊓ centSub W) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h2] at h1
    exact h1.symm
  set E : Subgroup (Perm (Fin n)) := S.range with hE
  have hE2 : ∀ b ∈ E, b * b = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hA2 a a.2)
    rw [this, map_one]
  have hnat : Nat.card E * Nat.card (altFix n E) ≤ Nat.card (altHeart n) :=
    (natFF (by omega : 5 ≤ n) hE2).2 fun h =>
      (Nat.not_even_iff_odd.2 hodd) ((natFF (by omega : 5 ≤ n) hE2).1 h).1
  set F : Subgroup V := fixV A with hF
  have hinj : Nat.card ↥(F ⊓ M) ≤ Nat.card (altFix n E) := by
    let f : ↥(F ⊓ M) → ↥(altFix n E) := fun m =>
      ⟨(QuotientAddGroup.mk (Multiplicative.toAdd (D.e ⟨m.1, m.2.2⟩)) : altHeart n), by
        rw [mem_altFix_iff_altAct]
        rintro _ ⟨a, rfl⟩
        have h1 := hS1 a ⟨m.1, m.2.2⟩ ⟨m.1, m.2.2⟩ ((mem_fixV.1 m.2.1) a a.2).symm
        rw [altAct_mk, ← h1]⟩
    have hf : Function.Injective f := by
      intro m m' h
      have h1 : (QuotientAddGroup.mk (Multiplicative.toAdd (D.e ⟨m.1, m.2.2⟩)) : altHeart n) =
          QuotientAddGroup.mk (Multiplicative.toAdd (D.e ⟨m'.1, m'.2.2⟩)) :=
        congrArg Subtype.val h
      have h2 := altHeart_mk_injective hodd h1
      have h3 : (⟨m.1, m.2.2⟩ : ↥M) = ⟨m'.1, m'.2.2⟩ :=
        D.e.injective (Multiplicative.toAdd.injective h2)
      exact Subtype.ext (congrArg (fun x : ↥M => (x : V)) h3)
    exact Nat.card_le_card_of_injective f hf
  have hcardH : Nat.card (altHeart n) = Nat.card M := by
    have e1 : Nat.card ↥M = Nat.card (evenWeight n) :=
      (Nat.card_congr D.e.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
    have e2 : Nat.card (evenWeight n) = Nat.card (altHeart n) :=
      Nat.card_congr (Equiv.ofBijective (QuotientAddGroup.mk : evenWeight n → altHeart n)
        ⟨altHeart_mk_injective hodd, QuotientAddGroup.mk_surjective⟩)
    rw [e1, e2]
  have hrM : F.relIndex M * Nat.card ↥(F ⊓ M) = Nat.card M := Subgroup.relIndex_mul_card F M
  have hrW : F.relIndex W * Nat.card ↥(F ⊓ W) = Nat.card W := Subgroup.relIndex_mul_card F W
  have hposFM : 0 < Nat.card ↥(F ⊓ M) := Nat.card_pos
  have hposFW : 0 < Nat.card ↥(F ⊓ W) := Nat.card_pos
  have hEM : Nat.card E ≤ F.relIndex M := by
    have h1 : Nat.card E * Nat.card ↥(F ⊓ M) ≤ F.relIndex M * Nat.card ↥(F ⊓ M) := by
      calc Nat.card E * Nat.card ↥(F ⊓ M) ≤ Nat.card E * Nat.card (altFix n E) :=
            Nat.mul_le_mul_left _ hinj
        _ ≤ Nat.card (altHeart n) := hnat
        _ = Nat.card M := hcardH
        _ = F.relIndex M * Nat.card ↥(F ⊓ M) := hrM.symm
    exact Nat.le_of_mul_le_mul_right h1 hposFM
  have hrW0 : F.relIndex W ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrW
    exact (Nat.card_pos (α := W)).ne' hrW.symm
  have hEW : Nat.card E ≤ F.relIndex W :=
    hEM.trans (Subgroup.relIndex_le_of_le_right hMW hrW0)
  have hcomm' : Nat.card ↥(W ⊓ F) = Nat.card ↥(F ⊓ W) := by rw [inf_comm]
  rw [hcomm', hcardA]
  have hfin : Nat.card E * Nat.card ↥(F ⊓ W) ≤ Nat.card W := by
    rw [← hrW]; exact Nat.mul_le_mul_right _ hEW
  calc Nat.card ↥(A ⊓ centSub W) * Nat.card E * Nat.card ↥(F ⊓ W)
      = Nat.card ↥(A ⊓ centSub W) * (Nat.card E * Nat.card ↥(F ⊓ W)) := mul_assoc _ _ _
    _ ≤ Nat.card ↥(A ⊓ centSub W) * Nat.card W := Nat.mul_le_mul_left _ hfin

end Count

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
