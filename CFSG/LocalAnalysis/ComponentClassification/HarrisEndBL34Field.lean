module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34E4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Inputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem card_comm_mod_center (hL : LLayer hs π)
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    Nat.card {e : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) //
        (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ * g⁻¹ * e * g ∈
          GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))} =
      Nat.card ↥(centralizer {((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S) *
        Nat.card (GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
  have hn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := inferInstance
  set r : Equiv.Perm (Fin 42) := ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) with hr
  set Ys : Subgroup ↥PSL3Four.S := (centralizer {r}).comap PSL3Four.S.subtype with hYs
  set Y : Subgroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := Ys.comap π
    with hY
  have hA : ∀ e : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))),
      (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ * g⁻¹ * e * g ∈
        GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ↔ e ∈ Y := by
    intro e
    have hae : g⁻¹ * (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g⁻¹⁻¹ ∈
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
      hn.conj_mem _ e.2 _
    set a : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := ⟨_, hae⟩ with ha
    have hπa := hL.rho_conj g⁻¹ e a rfl
    rw [map_inv, Subgroup.coe_inv, inv_inv, ← hr] at hπa
    have heq : (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ * g⁻¹ * e * g =
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype (e⁻¹ * a) := by
      rw [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, ha]
      group
    rw [heq, zStarIn_eq, mem_map_iff_mem (subtype_injective _), ← hL.ker, MonoidHom.mem_ker,
      hY, mem_comap, hYs, mem_comap, Subgroup.coe_subtype, mem_centralizer_singleton_iff,
      map_mul, map_inv, inv_mul_eq_one]
    constructor
    · intro h
      have h1 : (π e : Equiv.Perm (Fin 42)) = π a := congrArg Subtype.val h
      rw [← hπa] at h1
      calc (π e : Equiv.Perm (Fin 42)) * r = r * (r⁻¹ * (π e : Equiv.Perm (Fin 42)) * r) := by
            group
        _ = r * π e := by rw [← h1]
    · intro h
      apply Subtype.ext
      rw [← hπa]
      calc (π e : Equiv.Perm (Fin 42)) = r⁻¹ * (r * π e) := by group
        _ = r⁻¹ * ((π e : Equiv.Perm (Fin 42)) * r) := by rw [h]
        _ = r⁻¹ * π e * r := by group
  have hYs' : Nat.card Ys = Nat.card ↥(centralizer {r} ⊓ PSL3Four.S) := by
    rw [hYs, ← Subgroup.subgroupOf, ← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have hZ : Nat.card (GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) =
      Nat.card π.ker := by
    rw [zStarIn_eq, hL.ker, Subgroup.card_map_of_injective (subtype_injective _)]
  rw [hZ, Nat.card_congr (Equiv.subtypeEquivRight hA)]
  change Nat.card ↥Y = _
  rw [hY, hL.card_comap_pi Ys, hYs', mul_comm]

theorem isL34Field (hL : LLayer hs π) :
    IsL34Field (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) := by
  have hn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := inferInstance
  obtain ⟨-, hrtS⟩ := hL.rho_t_facts
  refine ⟨?_, by rw [← sq]; exact hs.tBar_sq, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro e
    refine ⟨fun he => hn.conj_mem e he _, fun he => ?_⟩
    have := hn.conj_mem _ he (hs.setup.tBar i j)⁻¹
    rwa [show (hs.setup.tBar i j)⁻¹ * (hs.setup.tBar i j * e * (hs.setup.tBar i j)⁻¹) *
      (hs.setup.tBar i j)⁻¹⁻¹ = e by group] at this
  · rw [hL.withKernel_eq, ← hL.rho_mem_S_iff]
    exact hrtS
  · rw [hL.card_comm_mod_center, hL.card_centralizer_rho_t]

theorem not_conj_tz
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (hQE : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (c : X) :
    c * t * c⁻¹ ≠ t * z := by
  intro hc
  obtain ⟨x, hxD, hx2, hxM, h0, h1⟩ := hL.exists_x hZ
  have hx1 : x ≠ 1 := by
    rintro rfl
    have : (QuotientGroup.mk ⟨1, hxM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 1 := rfl
    exact h0 ((hL.rho_mem_S_iff _).mpr (by rw [this]; exact one_mem _))
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer (mem_inf.mp hxD).2)
  obtain ⟨g₁, hg₁H, hg₁⟩ := hs.setup.exists_conj_eq_z hKF hxD hx2 hx1
  have hg₁t : g₁⁻¹ * t * g₁ = t := by
    rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hg₁H]
    group
  have hg₁x : g₁⁻¹ * z * g₁ = x := by rw [← hg₁]; group
  refine hL.false_of_conj_xt hFC hKC hI hKF hUC hZ hQE hxD hx2 hxM h0 h1 (c := g₁⁻¹ * c) ?_
  calc g₁⁻¹ * c * t * (g₁⁻¹ * c)⁻¹ = g₁⁻¹ * (c * t * c⁻¹) * g₁ := by group
    _ = g₁⁻¹ * (t * z) * g₁ := by rw [hc]
    _ = (g₁⁻¹ * t * g₁) * (g₁⁻¹ * z * g₁) := by group
    _ = x * t := by rw [hg₁t, hg₁x, hxt]

theorem _root_.CFSG.ComponentClassification.HarrisLit.EndB.eq_of_comm_Dstar
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hs : Setting46e t L p f S w z V i j) {d : X}
    (hd : d ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hc : ∀ e ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      d * e = e * d) : d = 1 ∨ d = z := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hs.setup.dihedral_Dstar hFC hKC i j
  have hz := hs.setup.z_mem_Dstar hFC hKC i j
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hne : (2 : ℕ) ^ m ≠ 2 := by
    intro h
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hr2 : (DihedralGroup.r (((2 ^ m / 2 : ℕ)) : ZMod (2 ^ m))) ^ 2 = 1 := by
    have hk : (((2 ^ m / 2) * 2 : ℕ) : ZMod (2 ^ m)) = 0 := by
      rw [Nat.div_mul_cancel h2]
      exact ZMod.natCast_self _
    rw [DihedralGroup.r_pow, ← DihedralGroup.r_zero]
    congr 1
    exact_mod_cast hk
  have hcen : ∀ a : ↥(S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      (∀ b : ↥(S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
        a * b = b * a) →
      e a = 1 ∨ e a = DihedralGroup.r (((2 ^ m / 2 : ℕ)) : ZMod (2 ^ m)) := by
    intro a ha
    have hmem : e a ∈ center (DihedralGroup (2 ^ m)) := mem_center_iff.mpr fun g => by
      obtain ⟨b, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, ha b]
    rw [DihedralGroup.center_eq_closure_of_even_ne_two (even_iff_two_dvd.2 h2) hne] at hmem
    exact EndB.eq_one_or_eq_of_mem_zpowers_sq hr2 hmem
  have hz1 : z ≠ 1 := by
    intro h
    have := hs.setup.z_order
    rw [h, orderOf_one] at this
    norm_num at this
  rcases hcen ⟨d, hd⟩ (fun b => Subtype.ext (hc b b.2)) with h | h
  · left
    have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
    exact this
  · right
    rcases hcen ⟨z, hz⟩ (fun b => Subtype.ext (hs.setup.z_comm_D (mem_inf.mp b.2).1).symm) with
      h' | h'
    · exact absurd (congrArg Subtype.val (e.injective (h'.trans (map_one e).symm))) hz1
    · exact congrArg Subtype.val (e.injective (h.trans h'.symm))

theorem mem_T_layer (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥) {τ : X}
    (hτT : τ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
    (hτM : τ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (hτE : (QuotientGroup.mk ⟨τ, hτM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
    τ ∈ (S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ds := S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) with hDs
  set T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w with hT
  set A := T ⊓ preimageOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) with hA
  have hT1 : IsSylowOf 2 T (centralizer ({t} : Set X) ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) :=
    hs.lemma45.isSylowOf_T
  have hTM : T ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    hT1.le.trans inf_le_right
  have hTH : T ≤ centralizer ({t} : Set X) := hT1.le.trans inf_le_left
  have hDsM : Ds ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    fun d hd => K_le_centralizer_beta i j (mem_inf.mp hd).2
  have hDsT : Ds ≤ T := fun d hd => mem_sup_left (mem_sup_right (mem_inf.mp hd).1)
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) ^ 2 = 1 :=
    hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hβT : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ T := hs.setup.X_le_T (beta_mem_X i j)
  have hβM : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈
      centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    mem_centralizer_singleton_iff.mpr rfl
  have hBA : Ds ⊔ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤ A := by
    refine sup_le (fun d hd => mem_inf.mpr ⟨hDsT hd, (mem_preimageOf (hDsM hd)).mpr ?_⟩)
      (zpowers_le.mpr (mem_inf.mpr ⟨hβT, (mem_preimageOf hβM).mpr ?_⟩))
    · exact hs.KBar_le_layer ⟨⟨d, hDsM hd⟩, (mem_inf.mp hd).2, rfl⟩
    · obtain ⟨b, -, hb⟩ := hL.h412.lemma46c.2.2 hZ
      have hb' : (QuotientGroup.mk ⟨_, hβM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = b :=
        hb.symm
      rw [hb']
      exact b.2
  obtain ⟨-, -, -, ⟨eD⟩⟩ := hL.seven hZ
  have hD16 : Nat.card ↥(S ⊓ L) = 16 := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
    norm_num
  have hDs8 : Nat.card Ds = 8 := by
    have h1 := Subgroup.relIndex_mul_card Ds (S ⊓ L)
    rw [hs.setup.relIndex_Dstar hFC hKC i j, inf_of_le_left (inf_le_left : Ds ≤ S ⊓ L),
      hD16] at h1
    rw [hDs]
    omega
  have hβDs : w ^ (orderOf w / 2) * t ^ i * z ^ j ∉ Ds :=
    fun h => hs.beta.not_mem (mem_sup_right (mem_inf.mp h).1)
  have hB16 := EndB.card_sup_zpowers (K := Ds) (u := w ^ (orderOf w / 2) * t ^ i * z ^ j)
    (fun k hk => by
      rw [(mem_centralizer_singleton_iff.mp (hDsM hk)).symm, mul_inv_cancel_right]
      exact hk) (by rw [hβ2]; exact one_mem _) hβDs
  rw [hDs8] at hB16
  have hAM : A ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    inf_le_left.trans hTM
  have hA2 : IsPGroup 2 A := hT1.isPGroup.to_le inf_le_left
  have hAle : Nat.card A ≤ 16 := by
    have hbar : barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) A ≤
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j} := by
      rintro _ ⟨a, ha, rfl⟩
      refine mem_inf.mpr ⟨(mem_preimageOf a.2).mp (mem_inf.mp ha).2, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact EndB.mk_comm a.2 (hs.setup.t_mem_centralizer_beta i j)
        (mem_centralizer_singleton_iff.mp (hTH (mem_inf.mp ha).1))
    have h2 : IsPGroup 2
        (barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) A) := by
      have : IsPGroup 2 ↥(A.subgroupOf
          (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) :=
        hA2.of_equiv (subgroupOfEquivOfLe hAM).symm
      exact this.map _
    have h1 := card_le_twoPart h2 hbar
    rw [card_barOf hAM hA2, twoPart, hL.card_layer_inf_centralizer hZ,
      show (336 : ℕ) = 2 ^ 4 * 21 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)] at h1
    exact h1
  have heq : A = Ds ⊔ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    (Subgroup.eq_of_le_of_card_ge hBA (by omega)).symm
  have hτA : τ ∈ A := mem_inf.mpr ⟨hτT, (mem_preimageOf hτM).mpr hτE⟩
  rw [heq] at hτA
  exact hτA

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit
