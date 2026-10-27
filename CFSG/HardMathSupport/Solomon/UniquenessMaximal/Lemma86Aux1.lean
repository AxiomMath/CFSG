module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.FrattiniAction
public import CFSG.Quasithin.Vol2.Ch10SecQ9H54
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def conjAut {Q N : Subgroup G} (hN : N ≤ Subgroup.normalizer (Q : Set G)) :
    ↥N →* MulAut ↥Q :=
  Q.normalizerMonoidHom.comp (Subgroup.inclusion hN)

omit [Finite G] in
theorem conjAut_apply {Q N : Subgroup G} (hN : N ≤ Subgroup.normalizer (Q : Set G)) (n : N)
    (q : Q) : ((conjAut hN n q : Q) : G) = n * q * (n : G)⁻¹ := rfl

@[reducible] noncomputable def fqComm {Q : Subgroup G} (hQ : IsPGroup 2 Q) :
    CommGroup (↥Q ⧸ frattini ↥Q) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  { (inferInstance : Group (↥Q ⧸ frattini ↥Q)) with
    mul_comm := fun a b => (CFSG.GroupTheory.frattini_elementary_quotient hQ).2.1.is_comm.comm a b }

noncomputable def fqRho {Q N : Subgroup G} (hN : N ≤ Subgroup.normalizer (Q : Set G)) :
    ↥N →* MulAut (↥Q ⧸ frattini ↥Q) where
  toFun n := QuotientGroup.congr (frattini ↥Q) (frattini ↥Q) (conjAut hN n)
    (CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv.map_frattini_mulEquiv _)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.congr_mk, map_one]
    rfl
  map_mul' g h := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.congr_mk, map_mul]
    rfl

structure LinPkg (Q N : Subgroup G) where
  V : Type
  [comm : CommGroup V]
  [fin : Finite V]
  elem : IsElemAbelianTwo V
  π : ↥Q →* V
  ρ : ↥N →* MulAut V
  π_surj : Function.Surjective π
  norm : ∀ (n : N) (q : Q), (n : G) * q * (n : G)⁻¹ ∈ Q
  ρ_π : ∀ (n : N) (q q' : Q), (n : G) * q * (n : G)⁻¹ = q' → ρ n (π q) = π q'
  ker_iff : ∀ n : N, ρ n = 1 ↔ (n : G) ∈ Q

attribute [instance] LinPkg.comm LinPkg.fin

noncomputable def LinPkg.ofCore {Q N : Subgroup G} (hQ2 : IsPGroup 2 Q)
    (hN : N ≤ Subgroup.normalizer (Q : Set G)) (hQ : Q = pCoreOf 2 N)
    (hC : N ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) : LinPkg Q N :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (IsPGroup 2 ↥Q) := ⟨hQ2⟩
  letI : CommGroup (↥Q ⧸ frattini ↥Q) := fqComm hQ2
  { V := ↥Q ⧸ frattini ↥Q
    elem := by
      intro v
      have := (CFSG.GroupTheory.frattini_elementary_quotient hQ2).2.2.1 v
      rw [pow_two] at this
      exact this
    π := QuotientGroup.mk' (frattini ↥Q)
    ρ := fqRho hN
    π_surj := QuotientGroup.mk'_surjective _
    norm := fun n q => (conjAut hN n q).2
    ρ_π := by
      intro n q q' h
      show QuotientGroup.congr (frattini ↥Q) (frattini ↥Q) (conjAut hN n)
        (CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv.map_frattini_mulEquiv _)
        (QuotientGroup.mk q) = QuotientGroup.mk q'
      rw [QuotientGroup.congr_mk]
      congr 1
      exact Subtype.ext (by rw [conjAut_apply]; exact h)
    ker_iff := by
      intro n
      constructor
      · intro h1
        have hn : (n : G) ∈ N := n.2
        refine CFSG.HardMathSupport.Solomon.UniquenessMaximal.mem_of_commutator_mem_frattini hQ hC hn ?_
        intro q hq
        have h2 := congrArg (fun φ : MulAut (↥Q ⧸ frattini ↥Q) => φ (QuotientGroup.mk ⟨q, hq⟩)) h1
        simp only [MulAut.one_apply] at h2
        change QuotientGroup.congr (frattini ↥Q) (frattini ↥Q) (conjAut hN n)
          (CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv.map_frattini_mulEquiv _)
          (QuotientGroup.mk ⟨q, hq⟩) = QuotientGroup.mk ⟨q, hq⟩ at h2
        rw [QuotientGroup.congr_mk] at h2
        have h3 := (QuotientGroup.eq_iff_div_mem).1 h2
        refine ⟨_, h3, ?_⟩
        simp [conjAut_apply, div_eq_mul_inv]
      · intro hnQ
        ext x
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
        change QuotientGroup.congr (frattini ↥Q) (frattini ↥Q) (conjAut hN n)
          (CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv.map_frattini_mulEquiv _)
          (QuotientGroup.mk x) = QuotientGroup.mk x
        rw [QuotientGroup.congr_mk]
        refine (QuotientGroup.eq_iff_div_mem).2 ?_
        have hc := CFSG.commutator_le_frattini_of_isPGroup (R := ↥Q) (p := 2)
        refine hc (Subgroup.commutator_mem_commutator (g₁ := (⟨n, hnQ⟩ : Q)) (g₂ := x)
          (Subgroup.mem_top _) (Subgroup.mem_top _)) |> fun h => ?_
        convert h using 1
        apply Subtype.ext
        simp [conjAut_apply, div_eq_mul_inv, commutatorElement_def] }

namespace LinPkg

variable {Q N : Subgroup G} (P : LinPkg Q N)

omit [Finite G] in
theorem eq_one_of_pow_eq_one (hQ2 : IsPGroup 2 Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : N} (hn : n ^ p = 1) (h : P.ρ n = 1) : n = 1 := by
  have hnQ : (n : G) ∈ Q := (P.ker_iff n).1 h
  obtain ⟨k, hk⟩ := hQ2 ⟨(n : G), hnQ⟩
  have h1 : (n : G) ^ p = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h2 : (n : G) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hd : orderOf (n : G) ∣ p := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf (n : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have h3 : orderOf (n : G) = 1 :=
    Nat.eq_one_of_dvd_one (by simpa [Nat.Coprime.gcd_eq_one hcop] using Nat.dvd_gcd hd hd2)
  have h4 : (n : G) = 1 := orderOf_eq_one_iff.1 h3
  exact Subtype.ext h4

omit [Finite G] in
theorem isPGroup_ker (hQ2 : IsPGroup 2 Q) : IsPGroup 2 ↥P.ρ.ker := by
  let f : ↥P.ρ.ker →* ↥Q :=
    MonoidHom.codRestrict (N.subtype.comp P.ρ.ker.subtype) Q (fun n => (P.ker_iff n.1).1 n.2)
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : ↥Q => (x : G)) h
  exact hQ2.of_injective f hf

omit [Finite G] in
theorem pCoreOf_range_eq_bot (hQ2 : IsPGroup 2 Q) (hQ : Q = pCoreOf 2 N) :
    pCoreOf 2 P.ρ.range = ⊥ := by
  have hker := P.isPGroup_ker hQ2
  set R : Subgroup (MulAut P.V) := pCoreOf 2 P.ρ.range with hR
  have hRp : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P.ρ.range
  have hRX : R ≤ P.ρ.range := CFSG.LieType.BorelTits.pCoreOf_le 2 P.ρ.range
  have hXR : P.ρ.range ≤ Subgroup.normalizer (R : Set (MulAut P.V)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P.ρ.range
  set Rh : Subgroup ↥N := R.comap P.ρ with hRh
  have hRhp : IsPGroup 2 ↥Rh := hRp.comap_of_ker_isPGroup P.ρ hker
  have hRhn : Rh.Normal := by
    refine ⟨fun r hr g => ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (hXR ⟨g, rfl⟩) (P.ρ r)).1 hr
    show P.ρ (g * r * g⁻¹) ∈ R
    simpa using this
  set C : Subgroup G := Rh.map N.subtype with hC
  have hCN : C ≤ N := Subgroup.map_subtype_le _
  have hCnorm : N ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨g, hg⟩ * r * ⟨g, hg⟩⁻¹, hRhn.conj_mem r hr _, by simp⟩
    · rintro ⟨r, hr, hrx⟩
      refine ⟨⟨g, hg⟩⁻¹ * r * ⟨g, hg⟩, by simpa using hRhn.conj_mem r hr ⟨g, hg⟩⁻¹, ?_⟩
      have h1 : (r : G) = g * x * g⁻¹ := hrx
      simp [h1, mul_assoc]
  have hC2 : IsPGroup 2 C := hRhp.map _
  have hCQ : C ≤ Q := hQ ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCN hCnorm hC2
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨n, rfl⟩ := hRX hr
  have hn : n ∈ Rh := hr
  have hnQ : (n : G) ∈ Q := hCQ ⟨n, hn, rfl⟩
  exact Subgroup.mem_bot.2 ((P.ker_iff n).2 hnQ)

end LinPkg

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
