module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTy
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6CentPGU
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClAsm
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClU6Pair

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram isPrimeFormGram_idGram)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (hF4)
open CFSG.Fischer (F4)

private theorem ringAutF4_eq_one_of_pow {m : ℕ} (hm : Nat.Coprime 2 m) {σ : F4 ≃+* F4}
    (hσ : σ ^ m = 1) : σ = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
    Nat.prime_two (n := 2) (by norm_num) (hF4.card.trans (by norm_num))
  have h1 : orderOf σ ∣ 2 := hcard ▸ orderOf_dvd_natCard σ
  have h3 : orderOf σ ∣ 1 := by
    have := Nat.dvd_gcd h1 (orderOf_dvd_of_pow_eq_one hσ)
    rwa [Nat.Coprime.gcd_eq_one hm] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem qsBRes_u6two {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (hN : QSNL 3 S B T x D K) (hS : catalogIs (PSimple 3 S) S9.isU6two)
    (hK : catalogIs (PSimple 3 K) S9.isU5two ∨ catalogIs (PSimple 3 K) S9.isU6two)
    (hB : Nat.card B = 3 ^ 5)
    (hc : ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω)) : QSConcl 3 S B D K := by
  have h := hN.cfg
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 h.normal) ▸ Subgroup.mem_top g
  obtain ⟨e₁⟩ := HSubT.nonempty_S6_of_isU6two hS
  obtain ⟨ι, -⟩ : ∃ ι : PSimple 3 S ≃* primeFormP hF4 (idGram F4 6),
      ι = e₁.trans KU6Cent.e6 := ⟨_, rfl⟩
  haveI : Finite (primeFormP hF4 (idGram F4 6)) := Finite.of_equiv _ ι.toEquiv
  obtain ⟨κ, hκdef⟩ : ∃ κ : PSimple 3 S →* MulAut (primeFormP hF4 (idGram F4 6)),
      ∀ z, κ z = MulAut.conj (ι z) := ⟨MulAut.conj.comp ι.toMonoidHom, fun _ => rfl⟩
  have hcen := center_pSimple_eq_bot Nat.prime_three h.comp
  have hκ : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ Subgroup.center (PSimple 3 S) := Subgroup.mem_center_iff.2 fun w => by
      have h1 := congrArg (fun φ : MulAut (primeFormP hF4 (idGram F4 6)) => φ (ι w)) hz
      simp only [hκdef, MulAut.conj_apply, MulAut.one_apply] at h1
      apply ι.injective
      rw [map_mul, map_mul]
      calc ι w * ι z = ι z * ι w * (ι z)⁻¹ * ι z := by rw [h1]
        _ = ι z * ι w := by group
    rw [hcen] at hzc
    exact Subgroup.mem_bot.1 hzc
  have hκD : ∀ z, κ z ∈ primeFormD hF4 (idGram F4 6) := fun z => by
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (ι z)
    exact ⟨⟨s, s.2.1⟩, (primeFormConjHom_eq_conj hF4 _ s).trans (by rw [hκdef, ← hs])⟩
  obtain ⟨eS, heS⟩ : ∃ eS : PSimple 3 S →* ↥(primeFormD hF4 (idGram F4 6)),
      ∀ z, (eS z : MulAut (primeFormP hF4 (idGram F4 6))) = κ z :=
    ⟨κ.codRestrict _ hκD, fun _ => rfl⟩
  have hconj : ∀ (β : MulAut (primeFormP hF4 (idGram F4 6))) (z : PSimple 3 S),
      β * κ z * β⁻¹ = κ (ι.symm (β (ι z))) := fun β z => by
    ext p
    simp only [hκdef, MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have hcomm : ∀ (β : MulAut (primeFormP hF4 (idGram F4 6))) (z : PSimple 3 S),
      κ z * β = β * κ z ↔ β (ι z) = ι z := fun β z => by
    rw [eq_comm, ← mul_inv_eq_iff_eq_mul, hconj, hκ.eq_iff, MulEquiv.symm_apply_eq]
  have hfixc : ∀ g : ↥(primeFormD hF4 (idGram F4 6)),
      (Subgroup.centralizer ({g} : Set ↥(primeFormD hF4 (idGram F4 6)))).comap eS =
        (fixSubgroup (g : MulAut (primeFormP hF4 (idGram F4 6)))).comap ι.toMonoidHom := by
    intro g
    ext z
    rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      mem_fixSubgroup, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul, heS]
    exact hcomm g z
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Ω →* MulAut (primeFormP hF4 (idGram F4 6)),
      ∀ g, Ψ g = MulAut.congr ι (chevAut 3 S ⟨g, hSN g⟩) :=
    ⟨(MulAut.congr ι).toMonoidHom.comp ((chevAut 3 S).comp
      ((MonoidHom.id Ω).codRestrict _ hSN)), fun _ => rfl⟩
  have hker := ker_primeFormFieldFactor hF4 (isPrimeFormGram_idGram (K := F4) (n := 6))
    (by norm_num) (by norm_num)
  set χ : Ω →* (F4 ≃+* F4) := (primeFormFieldFactor hF4
    (isPrimeFormGram_idGram (K := F4) (n := 6)) (by norm_num) (by norm_num)).comp Ψ
  have hWD : ∀ w : χ.ker, Ψ w ∈ primeFormD hF4 (idGram F4 6) := fun w => by
    rw [← hker]
    exact w.2
  obtain ⟨ρ, hρ⟩ : ∃ ρ : χ.ker →* ↥(primeFormD hF4 (idGram F4 6)),
      ∀ w, (ρ w : MulAut (primeFormP hF4 (idGram F4 6))) = Ψ w :=
    ⟨(Ψ.comp χ.ker.subtype).codRestrict _ hWD, fun _ => rfl⟩
  have hodd : ∀ (g : Ω) (m : ℕ), Nat.Coprime 2 m → g ^ m = 1 → g ∈ χ.ker := fun g m hm hg =>
    MonoidHom.mem_ker.2 (ringAutF4_eq_one_of_pow hm (by rw [← map_pow, hg, map_one]))
  have hBW : B ≤ χ.ker := fun b hb => hodd b 3 (by decide) (h.elem.2 b hb)
  refine qsConcl_of_section h hK hB hc (eS := eS)
    (fun a b hab => hκ (by rw [← heS, ← heS, hab])) (W := χ.ker) ρ
    (fun w hw z => Subtype.ext ?_) (fun w hw => ?_) hBW
    ((Subgroup.commutator_mono le_top hBW).trans (Subgroup.commutator_le_right ⊤ χ.ker))
    (fun y _ hy => hodd y 11 (by decide) (by rw [← hy]; exact pow_orderOf_eq_one y))
    fun A T₁ d y hA h81 hdA hd1 hy hy1 hdy hT hT1 hAT => ?_
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, heS, heS, hρ, hΨ, hconj]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  · rw [Subtype.ext_iff, hρ, hΨ, Subgroup.coe_one, MulEquiv.map_eq_one_iff]
  · obtain ⟨_, ⟨e, heA, rfl⟩, hec, hlay⟩ := exists_layer_pair_u6 hF4
      (A := A.map (primeFormD hF4 (idGram F4 6)).subtype)
      (V := T₁.map (primeFormD hF4 (idGram F4 6)).subtype)
      (d := (d : MulAut (primeFormP hF4 (idGram F4 6)))) (y := y) (hA.map _)
      (by rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)])
      (Subgroup.map_subtype_le A) (Subgroup.mem_map_of_mem _ hdA)
      (fun h1 => hd1 (Subtype.ext h1)) y.2 (by rw [← Subgroup.coe_pow, hy, Subgroup.coe_one])
      (fun h1 => hy1 (Subtype.ext h1)) (congrArg Subtype.val hdy) (hT.map _)
      (fun h0 => hT1 ((Subgroup.map_eq_bot_iff_of_injective _
        (Subgroup.subtype_injective _)).1 h0))
      (Subgroup.map_subtype_le T₁) (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨v, hv, rfl⟩
        exact ⟨a * v * a⁻¹, (Subgroup.mem_normalizer_iff.1 (hAT ha) v).1 hv, by simp⟩)
    refine ⟨e, heA, fun he => hec (congrArg Subtype.val he), ?_⟩
    rw [Subgroup.comap_inf, hfixc, hfixc, ← Subgroup.comap_inf]
    exact glaPLayer_comap_ne_bot_of_equiv ι hlay

theorem qsBResU6two_holds : QSBResU6two :=
  fun _ _ _ _ _ _ _ _ _ hN hS hK hB hc => qsBRes_u6two hN hS hK hB hc

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
