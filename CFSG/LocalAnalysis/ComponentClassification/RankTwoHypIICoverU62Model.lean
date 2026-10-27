module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU62Facts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverSylow
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import CFSG.LargeExtraspecial.SMod20AutReal
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Fischer.T46Simple
public import CFSG.Fischer.Polar.Basic
public import CFSG.RankThree.PartOne.KP.Fi22Unitary
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.Monster.Code.Weights

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoHypIICover.U62

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Sporadic.Schreier (evalCodes evalCodes_mem)
open CFSG.Fischer (T46 t46G tvP)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LargeExtraspecial.SMod20.Aut (fieldPerm frob4 semiPerm)

section Abstract

variable {W : Type*} [Group W] [Finite W]

theorem yCensusII_of_sylowReps_inner {X : Subgroup W} (hX : X.Normal) (hXi : ¬ 4 ∣ X.index)
    (S : Sylow 2 W) {k : ℕ} (y : ℕ → W)
    (hrep : ∀ u ∈ (S : Subgroup W), u ∈ X → u ^ 2 = 1 → u ≠ 1 →
      ∃ j < k, ∃ c ∈ (S : Subgroup W), u = c * y j * c⁻¹)
    (hw : ∀ j < k, y j ∈ X → ∀ b ∈ (S : Subgroup W), b ^ 2 = 1 → b ∉ X →
      b * y j = y j * b → MonoW X false (closure {y j, b})) :
    YCensus X (· ≤ X) := by
  intro E hE hE4 hEX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hvE, hvX⟩ : ∃ v ∈ E, v ∉ X := by
    by_contra hcon
    push Not at hcon
    exact hEX hcon
  obtain ⟨a, haE, ha1, haX⟩ := exists_mem_of_not_four_dvd_index (X := X) hXi hE hE4
  obtain ⟨Q, hQ⟩ := (isPGroup_of_isElemAbelian hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W S Q
  have key : ∀ e ∈ E, g⁻¹ * e * g ∈ (S : Subgroup W) := by
    intro e he
    have h1 : e ∈ (Q : Subgroup W) := hQ he
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply] at h1
    exact h1
  have hconj2 : ∀ (h z : W), z ^ 2 = 1 → (h * z * h⁻¹) ^ 2 = 1 := fun h z hz => by
    rw [conj_pow, hz, mul_one, mul_inv_cancel]
  have ha2 : (g⁻¹ * a * g) ^ 2 = 1 := by
    have := hconj2 g⁻¹ a (hE.2 a haE)
    rwa [inv_inv] at this
  have ha'1 : g⁻¹ * a * g ≠ 1 := fun h1 => ha1 (by
    have := congrArg (fun z => g * z * g⁻¹) h1
    simpa [mul_assoc] using this)
  have haX' : g⁻¹ * a * g ∈ X := by
    have := hX.conj_mem a haX g⁻¹
    rwa [inv_inv] at this
  obtain ⟨j, hj, c, hcS, hcj⟩ := hrep _ (key a haE) haX' ha2 ha'1
  set h : W := c⁻¹ * g⁻¹ with hh
  have hxa : h * a * h⁻¹ = y j := by
    calc h * a * h⁻¹ = c⁻¹ * (g⁻¹ * a * g) * c := by rw [hh]; group
      _ = c⁻¹ * (c * y j * c⁻¹) * c := by rw [hcj]
      _ = y j := by group
  have hbS : h * v * h⁻¹ ∈ (S : Subgroup W) := by
    have e1 : h * v * h⁻¹ = c⁻¹ * (g⁻¹ * v * g) * c := by rw [hh]; group
    rw [e1]
    exact (S : Subgroup W).mul_mem ((S : Subgroup W).mul_mem ((S : Subgroup W).inv_mem hcS)
      (key v hvE)) hcS
  have hb2 : (h * v * h⁻¹) ^ 2 = 1 := hconj2 h v (hE.2 v hvE)
  have hbX : h * v * h⁻¹ ∉ X := fun hb => hvX (by
    have := hX.conj_mem _ hb h⁻¹
    simpa [mul_assoc] using this)
  have hyX : y j ∈ X := hxa ▸ hX.conj_mem a haX h
  have hcomm : h * v * h⁻¹ * y j = y j * (h * v * h⁻¹) := by
    rw [← hxa]
    have hva : v * a = a * v := congrArg Subtype.val (hE.1.is_comm.comm ⟨v, hvE⟩ ⟨a, haE⟩)
    calc h * v * h⁻¹ * (h * a * h⁻¹) = h * (v * a) * h⁻¹ := by group
      _ = h * (a * v) * h⁻¹ := by rw [hva]
      _ = h * a * h⁻¹ * (h * v * h⁻¹) := by group
  have hM := hw j hj hyX _ hbS hb2 hbX hcomm
  have hmap : closure ({y j, h * v * h⁻¹} : Set W) =
      (closure ({a, v} : Set W)).map (MulAut.conj h).toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxa]
  rw [hmap, monoW_map_conj_iff hX] at hM
  have hle : closure ({a, v} : Set W) ≤ E := by
    rw [closure_le]
    rintro z (rfl | rfl)
    · exact haE
    · exact hvE
  rcases monoW_mono hle hM with h' | ⟨h', -⟩
  · exact Or.inl h'
  · exact absurd h' (by decide)

end Abstract

theorem mem_normalizer_of_conj_mem' {H : Subgroup (Equiv.Perm (Fin 693))}
    {a : Equiv.Perm (Fin 693)} (h : ∀ g ∈ H, a * g * a⁻¹ ∈ H) :
    a ∈ Subgroup.normalizer (H : Set (Equiv.Perm (Fin 693))) := by
  have hle : H.map (MulAut.conj a).toMonoidHom ≤ H := by
    rintro _ ⟨g, hg, rfl⟩
    exact h g hg
  have heq : H.map (MulAut.conj a).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj a).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact h g
  · intro hg
    rw [← heq] at hg
    obtain ⟨g', hg', hgg'⟩ := hg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgg'
    have : g' = g := mul_left_cancel (mul_right_cancel hgg')
    rwa [← this]

theorem conj_mem_of_closure {S : Set (Equiv.Perm (Fin 693))} {H : Subgroup (Equiv.Perm (Fin 693))}
    {a : Equiv.Perm (Fin 693)} (h : ∀ g ∈ S, a * g * a⁻¹ ∈ H) {x : Equiv.Perm (Fin 693)}
    (hx : x ∈ closure S) : a * x * a⁻¹ ∈ H := by
  induction hx using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => rw [mul_one, mul_inv_cancel]; exact H.one_mem
  | mul x y _ _ hx hy =>
    have e : a * (x * y) * a⁻¹ = a * x * a⁻¹ * (a * y * a⁻¹) := by group
    rw [e]
    exact H.mul_mem hx hy
  | inv x _ hx =>
    have e : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
    rw [e]
    exact H.inv_mem hx

@[expose] def u62AutW : Subgroup (Equiv.Perm (Fin 693)) :=
  Subgroup.normalizer (T46 : Set (Equiv.Perm (Fin 693)))

theorem T46_le_u62AutW : T46 ≤ u62AutW := Subgroup.le_normalizer

theorem u62Let_mem :
    ∀ g ∈ u62Let, g ∈ T46 := by
  intro g hg
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
  exact CFSG.Fischer.t46G_mem _

theorem u62SbG_mem :
    ∀ g ∈ u62SbG, g ∈ T46 := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalCodes_mem T46 u62Let_mem w

theorem u62Sb_le_T46 :
    u62Sb ≤ T46 := by
  rw [u62Sb, closure_le]
  exact fun g hg => u62SbG_mem g hg

theorem centralizer_T46
    (hF : U62Facts) :
    Subgroup.centralizer (T46 : Set (Equiv.Perm (Fin 693))) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_centralizer_iff] at hz
  rw [Subgroup.mem_bot]
  have h0 : z 0 = 0 := (hF.1 (z 0)).1 fun g hg => by
    have h := congrArg (fun f : Equiv.Perm (Fin 693) => f 0) (hz g (u62SbG_mem g hg))
    simp only [Equiv.Perm.mul_apply] at h
    rw [h, (hF.1 0).2 rfl g hg]
  refine Equiv.ext fun q => ?_
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq T46 (0 : Fin 693) q
  have hx' : (x : Equiv.Perm (Fin 693)) 0 = q := hx
  have h := congrArg (fun f : Equiv.Perm (Fin 693) => f 0) (hz x x.2)
  simp only [Equiv.Perm.mul_apply, h0, hx'] at h
  rw [Equiv.Perm.one_apply]
  exact h.symm

@[expose] def u62AutConj : u62AutW →* MulAut T46 :=
  Subgroup.normalizerMonoidHom T46

theorem u62AutConj_apply (a : u62AutW) (g : T46) :
    ((u62AutConj a g : T46) : Equiv.Perm (Fin 693)) = a * g * (a : Equiv.Perm (Fin 693))⁻¹ :=
  rfl

theorem u62AutConj_injective
    (hF : U62Facts) : Function.Injective u62AutConj := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have hc : (a : Equiv.Perm (Fin 693)) ∈
      Subgroup.centralizer (T46 : Set (Equiv.Perm (Fin 693))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := congrArg (fun α : MulAut T46 => ((α ⟨h, hh⟩ : T46) : Equiv.Perm (Fin 693)))
      (MonoidHom.mem_ker.1 ha)
    simp only [u62AutConj_apply, MulAut.one_apply] at h1
    calc h * a = a * h * (a : Equiv.Perm (Fin 693))⁻¹ * a := by rw [h1]
      _ = a * h := by group
  rw [centralizer_T46 hF, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.2 (Subtype.ext hc)

theorem mem_u62AutW_of_conj {α : MulAut T46}
    {π : Equiv.Perm (Fin 693)} (h : ∀ g : T46, ((α g : T46) : Equiv.Perm (Fin 693)) = π * g * π⁻¹) :
    π ∈ u62AutW := by
  refine mem_normalizer_of_conj_mem' fun g hg => ?_
  rw [← h ⟨g, hg⟩]
  exact (α ⟨g, hg⟩).2

theorem u62AutConj_surjective :
    Function.Surjective u62AutConj := by
  intro α
  obtain ⟨A, φ, h⟩ := CFSG.LargeExtraspecial.SMod20.Aut.exists_semiPerm α
  refine ⟨⟨semiPerm A φ, mem_u62AutW_of_conj h⟩, ?_⟩
  ext g
  rw [u62AutConj_apply, h]

@[expose] def u62AutEquiv
    (hF : U62Facts) : u62AutW ≃* MulAut T46 :=
  MulEquiv.ofBijective u62AutConj ⟨u62AutConj_injective hF, u62AutConj_surjective⟩

theorem statedClassicalModel_T46 :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel T46 .PSU 6 2 1 :=
  ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, CFSG.Fischer.F4, inferInstance,
    inferInstance, by rw [Nat.card_eq_fintype_card, CFSG.Fischer.F4.card]; norm_num,
    ⟨CFSG.RankThree.PartOne.statedProjEquivT46.symm⟩⟩

theorem u62AutModel
    (hF : U62Facts) :
    AutModel ↥T46 ↥u62AutW (T46.subgroupOf u62AutW) :=
  autModel_of_conj T46_le_u62AutW (MulEquiv.refl _) (u62AutEquiv hF) u62AutConj_apply

theorem card_outer_T46_dvd :
    Nat.card (Outer T46) ∣ 6 := by
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inr rfl) (by norm_num) Nat.prime_two le_rfl statedClassicalModel_T46).1
  simpa [CFSG.RankThree.OuterOrder.determinantParameter] using hout

theorem finite_mulAut_T46 : Finite (MulAut T46) :=
  Finite.of_injective (fun α : MulAut T46 => (α : T46 → T46)) DFunLike.coe_injective

theorem card_u62AutW
    (hF : U62Facts) :
    Nat.card u62AutW = Nat.card (Outer T46) * 9196830720 := by
  have := finite_mulAut_T46
  rw [Nat.card_congr (u62AutEquiv hF).toEquiv, (inner T46).card_eq_card_quotient_mul_card_subgroup,
    ← CFSG.Fischer.card_T46]
  congr 1
  have hinj : Function.Injective (MulAut.conj : T46 →* MulAut T46) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hc : (g : Equiv.Perm (Fin 693)) ∈
        Subgroup.centralizer (T46 : Set (Equiv.Perm (Fin 693))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h1 := congrArg (fun α : MulAut T46 => ((α ⟨h, hh⟩ : T46) : Equiv.Perm (Fin 693)))
        (MonoidHom.mem_ker.1 hg)
      simp only [MulAut.conj_apply, MulAut.one_apply, coe_mul, coe_inv] at h1
      calc h * g = g * h * (g : Equiv.Perm (Fin 693))⁻¹ * g := by rw [h1]
        _ = g * h := by group
    rw [centralizer_T46 hF, Subgroup.mem_bot] at hc
    exact Subgroup.mem_bot.2 (Subtype.ext hc)
  exact Nat.card_range_of_injective hinj

theorem index_T46
    (hF : U62Facts) :
    (T46.subgroupOf u62AutW).index = Nat.card (Outer T46) := by
  have h := (T46.subgroupOf u62AutW).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T46_le_u62AutW).toEquiv,
    CFSG.Fischer.card_T46, card_u62AutW hF] at h
  omega

theorem frob4_symm_apply (x : CFSG.Fischer.F4) : frob4.symm x = frob4 x := rfl

theorem u62Phi_eq : u62Phi = semiPerm 1 frob4 := by
  rw [semiPerm, map_one, one_mul, u62Phi]

theorem frob4_symm : frob4.symm = frob4 := RingEquiv.ext frob4_symm_apply

theorem u62Phi_inv : u62Phi⁻¹ = u62Phi := by
  have e : (fieldPerm frob4)⁻¹ = fieldPerm frob4.symm := by
    ext p
    rfl
  rw [u62Phi, e, frob4_symm]

theorem u62Phi_mul_self : u62Phi * u62Phi = 1 := by
  nth_rewrite 1 [← u62Phi_inv]
  exact inv_mul_cancel _

theorem u62Phi_mem_u62AutW :
    u62Phi ∈ u62AutW := by
  refine mem_normalizer_of_conj_mem' fun g hg => ?_
  rw [CFSG.Fischer.T46_eq_closure] at hg
  refine conj_mem_of_closure (fun x hx => ?_) hg
  obtain ⟨p, rfl⟩ := hx
  rw [u62Phi_eq, CFSG.LargeExtraspecial.SMod20.Aut.semiPerm_tvP]
  exact CFSG.Fischer.tvP_mem _

@[expose] def u62S : Subgroup (Equiv.Perm (Fin 693)) :=
  closure ({g | g ∈ u62SbG} ∪ {u62Phi})

theorem u62Sb_le_u62S : u62Sb ≤ u62S :=
  closure_mono Set.subset_union_left

theorem u62Phi_mem_u62S : u62Phi ∈ u62S :=
  subset_closure (Set.mem_union_right _ rfl)

theorem conj_u62Phi_mem (hF : U62Facts) {s : Equiv.Perm (Fin 693)}
    (hs : s ∈ u62Sb) : u62Phi * s * u62Phi⁻¹ ∈ u62Sb := by
  have hs' : s ∈ closure {g | g ∈ u62SbG} := hs
  have hg : ∀ g ∈ {g | g ∈ u62SbG}, u62Phi * g * u62Phi⁻¹ ∈ u62Sb := hF.2.2.2.1
  exact conj_mem_of_closure hg hs'

theorem conj_u62Phi_mem' (hF : U62Facts) {s : Equiv.Perm (Fin 693)}
    (hs : s ∈ u62Sb) : u62Phi * s * u62Phi ∈ u62Sb := by
  have := conj_u62Phi_mem hF hs
  rwa [u62Phi_inv] at this

theorem mem_u62S_iff (hF : U62Facts)
    {x : Equiv.Perm (Fin 693)} : x ∈ u62S ↔ x ∈ u62Sb ∨ x * u62Phi ∈ u62Sb := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | rfl
      · exact Or.inl (subset_closure hg)
      · exact Or.inr (by rw [u62Phi_mul_self]; exact one_mem _)
    | one => exact Or.inl (one_mem _)
    | mul a b _ _ ha hb =>
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Or.inl (mul_mem ha hb)
      · exact Or.inr (by rw [mul_assoc]; exact mul_mem ha hb)
      · refine Or.inr ?_
        have e : a * b * u62Phi = a * u62Phi * (u62Phi * b * u62Phi) := by
          calc a * b * u62Phi = a * (u62Phi * u62Phi) * b * u62Phi := by
                rw [u62Phi_mul_self, mul_one]
            _ = a * u62Phi * (u62Phi * b * u62Phi) := by group
        rw [e]
        exact mul_mem ha (conj_u62Phi_mem' hF hb)
      · refine Or.inl ?_
        have e : a * b = a * u62Phi * (u62Phi * (b * u62Phi) * u62Phi) := by
          calc a * b = a * (u62Phi * u62Phi) * b * (u62Phi * u62Phi) := by
                rw [u62Phi_mul_self, mul_one, mul_one]
            _ = a * u62Phi * (u62Phi * (b * u62Phi) * u62Phi) := by group
        rw [e]
        exact mul_mem ha (conj_u62Phi_mem' hF hb)
    | inv a _ ha =>
      rcases ha with ha | ha
      · exact Or.inl (inv_mem ha)
      · refine Or.inr ?_
        have e : a⁻¹ * u62Phi = u62Phi * (a * u62Phi)⁻¹ * u62Phi := by
          rw [_root_.mul_inv_rev, u62Phi_inv]
          calc a⁻¹ * u62Phi = (u62Phi * u62Phi) * a⁻¹ * u62Phi := by
                rw [u62Phi_mul_self, one_mul]
            _ = u62Phi * (u62Phi * a⁻¹) * u62Phi := by group
        rw [e]
        exact conj_u62Phi_mem' hF (inv_mem ha)
  · rintro (hx | hx)
    · exact u62Sb_le_u62S hx
    · have := mul_mem (u62Sb_le_u62S hx) u62Phi_mem_u62S
      rwa [mul_assoc, u62Phi_mul_self, mul_one] at this

theorem card_u62S (hF : U62Facts) : Nat.card u62S = 65536 := by
  let f : u62Sb ⊕ u62Sb → u62S := fun
    | .inl s => ⟨s, u62Sb_le_u62S s.2⟩
    | .inr s => ⟨s * u62Phi, mul_mem (u62Sb_le_u62S s.2) u62Phi_mem_u62S⟩
  have hPhi : u62Phi ∉ u62Sb := hF.2.2.1
  have hbij : Function.Bijective f := by
    refine ⟨?_, fun x => ?_⟩
    · rintro (s | s) (t | t) h <;> simp only [f, Subtype.mk.injEq] at h
      · rw [Subtype.ext h]
      · exfalso
        apply hPhi
        have e : u62Phi = (t : Equiv.Perm (Fin 693))⁻¹ * s := by rw [h]; group
        rw [e]
        exact mul_mem (inv_mem t.2) s.2
      · exfalso
        apply hPhi
        have e : u62Phi = (s : Equiv.Perm (Fin 693))⁻¹ * t := by rw [← h]; group
        rw [e]
        exact mul_mem (inv_mem s.2) t.2
      · rw [Subtype.ext (mul_right_cancel h)]
    · rcases (mem_u62S_iff hF).1 x.2 with hx | hx
      · exact ⟨.inl ⟨x, hx⟩, rfl⟩
      · refine ⟨.inr ⟨_, hx⟩, Subtype.ext ?_⟩
        change (x : Equiv.Perm (Fin 693)) * u62Phi * u62Phi = x
        rw [mul_assoc, u62Phi_mul_self, mul_one]
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_sum, hF.2.1]

theorem u62Phi_not_mem_T46
    (hF : U62Facts) : u62Phi ∉ T46 := by
  intro h
  have hle : u62S ≤ T46 := by
    rw [u62S, closure_le]
    rintro g (hg | rfl)
    · exact u62SbG_mem g hg
    · exact h
  have hd := Subgroup.card_dvd_of_le hle
  rw [card_u62S hF, CFSG.Fischer.card_T46] at hd
  norm_num at hd

theorem mem_u62Sb_of_mem_T46
    (hF : U62Facts) {x : Equiv.Perm (Fin 693)} (hx : x ∈ u62S)
    (hxX : x ∈ T46) : x ∈ u62Sb := by
  rcases (mem_u62S_iff hF).1 hx with h | h
  · exact h
  · exfalso
    apply u62Phi_not_mem_T46 hF
    have e : u62Phi = x⁻¹ * (x * u62Phi) := by group
    rw [e]
    exact mul_mem (inv_mem hxX) (u62Sb_le_T46 h)

theorem u62S_le_u62AutW :
    u62S ≤ u62AutW := by
  rw [u62S, closure_le]
  rintro g (hg | rfl)
  · exact T46_le_u62AutW (u62SbG_mem g hg)
  · exact u62Phi_mem_u62AutW

theorem card_u62S_subgroupOf
    (hF : U62Facts) :
    Nat.card (u62S.subgroupOf u62AutW) = 65536 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe u62S_le_u62AutW).toEquiv, card_u62S hF]

theorem odd_index_u62S
    (hF : U62Facts) : ¬ 2 ∣ (u62S.subgroupOf u62AutW).index := by
  have h := (u62S.subgroupOf u62AutW).card_mul_index
  rw [card_u62S_subgroupOf hF, card_u62AutW hF] at h
  have hd := card_outer_T46_dvd
  have hpos : 0 < Nat.card (Outer T46) := Nat.pos_of_dvd_of_pos hd (by norm_num)
  have hle : Nat.card (Outer T46) ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  intro h2
  obtain ⟨m, hm⟩ := h2
  interval_cases hc : Nat.card (Outer T46) <;> omega

@[expose] def u62Sylow
    (hF : U62Facts) : Sylow 2 u62AutW :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (IsPGroup.of_card (n := 16) (by rw [card_u62S_subgroupOf hF]; norm_num) :
    IsPGroup 2 (u62S.subgroupOf u62AutW)).toSylow (odd_index_u62S hF)

theorem coe_u62Sylow
    (hF : U62Facts) :
    (u62Sylow hF : Subgroup u62AutW) = u62S.subgroupOf u62AutW := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.toSylow_coe _ (odd_index_u62S hF)

theorem not_four_dvd_index
    (hF : U62Facts) : ¬ 4 ∣ (T46.subgroupOf u62AutW).index := by
  rw [index_T46 hF]
  have hd := card_outer_T46_dvd
  have hpos : 0 < Nat.card (Outer T46) := Nat.pos_of_dvd_of_pos hd (by norm_num)
  have hle : Nat.card (Outer T46) ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  intro h4
  interval_cases hc : Nat.card (Outer T46) <;> omega

end CFSG.ComponentClassification.RankTwoHypIICover.U62
