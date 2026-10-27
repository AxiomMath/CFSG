module

import CFSG.Goldschmidt.Steps.Ind
import CFSG.Goldschmidt.Steps.Red1
import CFSG.Goldschmidt.Steps.Red2
import CFSG.Goldschmidt.Steps.IHConseq
import CFSG.Goldschmidt.Steps.GoldType
import CFSG.Goldschmidt.Steps.TICrit
import CFSG.Goldschmidt.Steps.PropHSetup
import CFSG.Walter.Bender1970
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG
public import CFSG.LocalAnalysis.ComponentClassification.Components
public import CFSG.Walter.SimpleCase

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace G41

variable {G : Type} [Group G]

theorem exists_sylow_of_fusionIsSylowIn {T X : Subgroup G} (hTX : fusionIsSylowIn 2 T X) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = T.subgroupOf X := by
  obtain ⟨hTX, hT, hmax⟩ := hTX
  refine ⟨⟨T.subgroupOf X, hT.comap_subtype, fun {Q} hQ hTQ => ?_⟩, rfl⟩
  have h1 := hmax (Q.map X.subtype) (Subgroup.map_subtype_le Q) (hQ.map X.subtype) fun s hs =>
    ⟨⟨s, hTX hs⟩, hTQ (show (⟨s, hTX hs⟩ : X) ∈ T.subgroupOf X from hs), rfl⟩
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q).symm

variable [Finite G]

theorem normalClosureIn_sylow_top {H A T : Subgroup G} (hTH : fusionIsSylowIn 2 T H)
    (hAT : A ≤ T) (hcl : IsStronglyClosedIn A T H) :
    (∃ P : Sylow 2 (normalClosureIn H A),
      (P : Subgroup (normalClosureIn H A)) = T.subgroupOf (normalClosureIn H A)) ∧
    Subgroup.normalClosure
      ((A.subgroupOf (normalClosureIn H A) : Subgroup (normalClosureIn H A)) :
        Set (normalClosureIn H A)) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAH : A ≤ H := hAT.trans hTH.1
  obtain ⟨PH, hPH⟩ := exists_sylow_of_fusionIsSylowIn hTH
  set M : Subgroup H := Subgroup.normalClosure ((A.subgroupOf H : Subgroup H) : Set H)
  have hMn : M.Normal := Subgroup.normalClosure_normal
  set K : Subgroup G := normalClosureIn H A
  let e : M ≃* K := M.equivMapOfInjective H.subtype H.subtype_injective
  have hes : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  have hAK : A ≤ K := fun a ha =>
    ⟨⟨a, hAH ha⟩, Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨P', hP'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal PH hMn.isSubnormal
    refine ⟨P'.mapSurjective hes, ?_⟩
    rw [Sylow.coe_mapSurjective]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : M.subtype y ∈ (PH : Subgroup H) ⊓ M := hP' ▸ ⟨y, hy, rfl⟩
      rw [hPH] at hy'
      exact hy'.1
    · intro hx
      set y : M := e.symm x
      have hyx : e y = x := e.apply_symm_apply x
      have hyT : M.subtype y ∈ (PH : Subgroup H) ⊓ M := by
        have h1 : ((y : H) : G) = (x : G) := by rw [← hyx]; rfl
        have h2 : (y : H) ∈ T.subgroupOf H := by
          rw [Subgroup.mem_subgroupOf, h1]
          exact hx
        refine Subgroup.mem_inf.2 ⟨?_, y.2⟩
        rw [hPH]
        exact h2
      rw [← hP'] at hyT
      obtain ⟨z, hz, hzy⟩ := hyT
      have hzy' : z = y := M.subtype_injective hzy
      exact ⟨z, hz, by rw [hzy']; exact hyx⟩
  ·
    have hA'P : A.subgroupOf H ≤ (PH : Subgroup H) := by
      rw [hPH]
      exact fun y hy => hAT hy
    have hclH : fusionStronglyClosed ((A.subgroupOf H : Subgroup H) : Set H)
        (PH : Subgroup H) := by
      intro a ha h hh
      rw [hPH] at hh
      exact hcl a ha h h.2 hh
    have hconj : ∀ c a : H, (a : G) ∈ A →
        ∃ m ∈ K, ∃ b ∈ A, ((c * a * c⁻¹ : H) : G) = m * b * m⁻¹ := by
      intro c a ha
      obtain ⟨m, hm, hmeq⟩ := exists_conj_normalClosure PH hA'P hclH c⁻¹
      have hy : c * a * c⁻¹ ∈ conjSub c⁻¹ (A.subgroupOf H) := by
        rw [mem_conjSub, show c⁻¹ * (c * a * c⁻¹) * c⁻¹⁻¹ = a by group]
        exact ha
      rw [hmeq, mem_conjSub] at hy
      refine ⟨((m⁻¹ : H) : G), ⟨m⁻¹, M.inv_mem hm, rfl⟩, ((m * (c * a * c⁻¹) * m⁻¹ : H) : G), hy,
        ?_⟩
      push_cast
      group
    set N := Subgroup.normalClosure ((A.subgroupOf K : Subgroup K) : Set K)
    have hle : M ≤ (N.map K.subtype).subgroupOf H := by
      change Subgroup.closure (Group.conjugatesOfSet ((A.subgroupOf H : Subgroup H) : Set H)) ≤ _
      rw [Subgroup.closure_le]
      intro y hy
      obtain ⟨a, ha, hay⟩ := Set.mem_iUnion₂.1 hy
      obtain ⟨c, rfl⟩ := isConj_iff.1 hay
      obtain ⟨m, hmK, b, hb, hmb⟩ := hconj c a ha
      refine ⟨⟨m, hmK⟩ * ⟨b, hAK hb⟩ * (⟨m, hmK⟩ : K)⁻¹, ?_, ?_⟩
      · exact Subgroup.normalClosure_normal.conj_mem _
          (Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 hb)) _
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
        exact hmb.symm
    rw [eq_top_iff]
    intro k _
    obtain ⟨y, hy, hyk⟩ := k.2
    obtain ⟨q, hq, hqy⟩ := hle hy
    have hkq : k = q := Subtype.ext (hyk.symm.trans hqy.symm)
    rw [hkq]
    exact hq

theorem isGoldType_of_component
    {Z : Type} [Group Z] [Finite Z] (S : Sylow 2 Z) {B L : Subgroup Z}
    (hB : IsMulCommutative B) (hL : IsComponentOf L ⊤)
    (htype : goldschmidtSimpleType (L ⧸ Subgroup.center L)) (hind : InducesOmega1 B L S)
    (hcov : ∀ a ∈ B, ∃ x ∈ B ⊓ L, ∀ y ∈ L, a⁻¹ * y * a = x⁻¹ * y * x) :
    IsGoldTypeI L ∨ IsGoldTypeII L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2
  rcases htype with h1 | h2 | h3 | hrest
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (Or.inl h2))
  · exact Or.inl (Or.inr (Or.inr h3))
  obtain ⟨SL, hSL⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  set SLh : Sylow 2 (L ⧸ Subgroup.center L) := SL.mapSurjective (QuotientGroup.mk'_surjective _)
    with hSLh
  obtain ⟨hSLhab, hSLhexp, -, -⟩ := GoldType.elementary_of_clauses hrest SLh
  have hkey : ∀ t : L, t ∈ (SL : Subgroup L) → ∃ x ∈ B, x ∈ L ∧
      x * (t : Z)⁻¹ ∈ Subgroup.centralizer (L : Set Z) := by
    intro t ht
    have htS : (t : Z) ∈ (S : Subgroup Z) ⊓ L := by
      rw [← hSL]
      exact ⟨t, ht, rfl⟩
    have ht2 : (t : Z) ^ 2 ∈ Subgroup.centralizer (L : Set Z) := by
      have h := hSLhexp (t : L ⧸ Subgroup.center L) (by
        rw [hSLh, Sylow.coe_mapSurjective]
        exact ⟨t, ht, rfl⟩)
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h' := congrArg Subtype.val (Subgroup.mem_center_iff.1 h ⟨y, hy⟩)
      simpa using h'
    obtain ⟨a, ha, hat⟩ := hind.2 t htS ht2
    obtain ⟨x, ⟨hxB, hxL⟩, hax⟩ := hcov a ha
    refine ⟨x, hxB, hxL, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := (hat y hy).symm.trans (hax y hy)
    calc y * (x * (t : Z)⁻¹) = x * (x⁻¹ * y * x) * (t : Z)⁻¹ := by group
      _ = x * ((t : Z)⁻¹ * y * t) * (t : Z)⁻¹ := by rw [h]
      _ = x * (t : Z)⁻¹ * y := by group
  have hcomm : ∀ c ∈ Subgroup.centralizer (L : Set Z), ∀ y ∈ L, Commute c y := fun c hc y hy =>
    (Subgroup.mem_centralizer_iff.1 hc y hy).symm
  have hSLab : IsMulCommutative (SL : Subgroup L) := by
    refine ⟨⟨fun t₁ t₂ => ?_⟩⟩
    obtain ⟨x₁, hx₁B, hx₁L, hc₁⟩ := hkey t₁ t₁.2
    obtain ⟨x₂, hx₂B, hx₂L, hc₂⟩ := hkey t₂ t₂.2
    apply Subtype.ext
    apply Subtype.ext
    have e₁ : (((t₁ : L) : Z)) = (x₁ * ((t₁ : L) : Z)⁻¹)⁻¹ * x₁ := by group
    have e₂ : (((t₂ : L) : Z)) = (x₂ * ((t₂ : L) : Z)⁻¹)⁻¹ * x₂ := by group
    have hc₂L : x₂ * ((t₂ : L) : Z)⁻¹ ∈ L := L.mul_mem hx₂L (L.inv_mem (t₂ : L).2)
    have k1 := hcomm _ (Subgroup.inv_mem _ hc₁) _ (L.inv_mem hc₂L)
    have k2 := hcomm _ (Subgroup.inv_mem _ hc₁) _ hx₂L
    have k3 := (hcomm _ (Subgroup.inv_mem _ hc₂) _ hx₁L).symm
    have k4 : Commute x₁ x₂ := congrArg Subtype.val (hB.is_comm.comm ⟨x₁, hx₁B⟩ ⟨x₂, hx₂B⟩)
    simp only [Subgroup.coe_mul]
    rw [e₁, e₂]
    exact ((k1.mul_right k2).mul_left (k3.mul_right k4)).eq
  have hodd : Odd (Nat.card (Subgroup.center L)) := CFSG.Walter.odd_card_center_of_perfect
    hL.2.2.1 (CFSG.Walter.hasAbelianSylowTwo_of_sylow SL hSLab)
  rcases hrest with hL2 | hree
  · exact Or.inr ⟨hodd, Or.inl hL2⟩
  have hab : CFSG.Walter.HasAbelianSylowTwo (L ⧸ Subgroup.center L) :=
    CFSG.Walter.hasAbelianSylowTwo_of_sylow SLh hSLhab
  have hnonab := (GoldType.sylow_of_ree_or_j1 hree SLh).1
  have hSC := CFSG.Walter.simpleCaseHyp_of_benderHyp CFSG.Walter.benderHyp
  rcases hSC _ inferInstance hnonab hab
      (fun H _ => CFSG.Walter.isAStar_of_hasAbelianSylowTwo hSC (hab.subgroup H)) with
    hL2 | hJR
  swap
  · exact Or.inr ⟨hodd, Or.inr hJR⟩
  rcases hL2 with ⟨f, hf, ⟨e⟩⟩ | hL2
  · rcases Nat.lt_or_ge f 3 with hf3 | hf3
    · obtain rfl : f = 2 := by omega
      have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨e'⟩ := CFSG.Walter.nonempty_psl2_five_mulEquiv_psl2_four
      exact Or.inr ⟨hodd, Or.inl
        ⟨5, 1, h5, ⟨2, rfl⟩, one_pos, by norm_num, Or.inr (by norm_num), ⟨e.trans e'.symm⟩⟩⟩
    · exact Or.inl (Or.inl ⟨f, hf3, ⟨e⟩⟩)
  · exact Or.inr ⟨hodd, Or.inl hL2⟩

theorem isSStarIn_of_lt
    {n : ℕ} (hIH : IH n) {H A T : Subgroup G} (hHn : Nat.card H < n)
    (hTH : fusionIsSylowIn 2 T H) (hAT : A ≤ T) (hA : IsMulCommutative A)
    (hcl : IsStronglyClosedIn A T H) : IsSStarIn H A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAH : A ≤ H := hAT.trans hTH.1
  refine ⟨hAH, hA, T, hTH, hAT, hcl, ?_⟩
  intro K
  obtain ⟨⟨PK, hPK⟩, htopK⟩ := normalClosureIn_sylow_top hTH hAT hcl
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hKn : Nat.card K < n := (Subgroup.card_le_of_le hKH).trans_lt hHn
  have hAPK : A.subgroupOf K ≤ (PK : Subgroup K) := by
    rw [hPK]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hAT (Subgroup.mem_subgroupOf.1 hx))
  have hclK : fusionStronglyClosed ((A.subgroupOf K : Subgroup K) : Set K) (PK : Subgroup K) := by
    rw [hPK]
    intro a ha k hk
    exact hcl a ha k (hKH k.2) hk
  have hC := (N1 n hIH K hKn).1 PK (A.subgroupOf K) hAPK (isMulCommutative_subgroupOf hA K) hclK
    htopK
  rw [hPK] at hC
  obtain ⟨h1, h3, -⟩ := hC
  obtain ⟨Sbar, hSbar, hclbar⟩ := CFSG.ShultStronglyClosedTI.quotient_stronglyClosed PK
    (A.subgroupOf K) (goldschmidtOddCore K) hAPK hclK
  have hBS : barOf K A ≤ (Sbar : Subgroup (K ⧸ goldschmidtOddCore K)) := by
    rw [hSbar]
    exact Subgroup.map_mono hAPK
  have hBab : IsMulCommutative (barOf K A) :=
    isMulCommutative_map (isMulCommutative_subgroupOf hA K) _
  have hBtop : Subgroup.normalClosure
      ((barOf K A : Subgroup (K ⧸ goldschmidtOddCore K)) : Set (K ⧸ goldschmidtOddCore K)) = ⊤ :=
    normalClosure_map_eq_top htopK _ (QuotientGroup.mk'_surjective _)
  have hO : goldschmidtOddCore (K ⧸ goldschmidtOddCore K) = ⊥ :=
    goldschmidtOddCore_quotient_eq_bot K
  have hcore : CoreHyp (K ⧸ goldschmidtOddCore K) Sbar (barOf K A) :=
    ⟨hBS, hBab, hclbar, hBtop, hO⟩
  have hO2B : CFSG.Open.pCore 2 (K ⧸ goldschmidtOddCore K) ≤ barOf K A := by
    show _ ≤ (A.subgroupOf K).map (QuotientGroup.mk' (goldschmidtOddCore K))
    rw [h3]
    exact le_sup_left
  refine ⟨h1, ?_, h3, ?_⟩
  ·
    have h18 := (N18 _ Sbar (barOf K A) hBS hBab hclbar hBtop).1
    exact fun x hx => h18 ⟨hO2B hx, hx⟩
  ·
    intro L hL
    have hidx : ((Subgroup.centralizer (L : Set (K ⧸ goldschmidtOddCore K))).subgroupOf
        (L ⊔ barOf K A)).index < n := by
      have hq : Nat.card (K ⧸ goldschmidtOddCore K) ≤ Nat.card K := by
        rw [← Subgroup.index_eq_card]
        exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
      calc _ ≤ Nat.card (L ⊔ barOf K A : Subgroup (K ⧸ goldschmidtOddCore K)) :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
        _ ≤ Nat.card (K ⧸ goldschmidtOddCore K) := Subgroup.card_le_card_group _
        _ < n := hq.trans_lt hKn
    obtain ⟨htype, hind⟩ := N21_of N19 n hIH _ Sbar (barOf K A) hcore L hL hidx
    exact isGoldType_of_component Sbar hBab hL htype hind
      (N17_of N11b _ Sbar (barOf K A) L hBS hBab hclbar hO hL htype hind)

end G41

open G41 in
theorem G41 :
    ∀ (G : Type) [Group G] [Finite G], IH (Nat.card G) → ∀ (S : Sylow 2 G) (U : Subgroup G),
      U ≤ S → IsMulCommutative U → fusionStronglyClosed (U : Set G) (S : Subgroup G) →
      ∀ H : Subgroup G, H ≠ ⊤ → ∃ g : G, U ⊓ H ≤ conjSub g U ∧ IsSStarIn H (conjSub g U ⊓ H) := by
  intro G _ _ hIH S U hUS hUab hUcl H hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 U := (S.isPGroup').to_le hUS
  obtain ⟨T, hUHT, hTH⟩ := TICrit.exists_fusionIsSylowIn (hU2.to_le inf_le_left)
    (inf_le_right : U ⊓ H ≤ H)
  obtain ⟨Q, hTQ⟩ := hTH.2.1.exists_le_sylow
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq G S Q
  have hTS : ∀ x ∈ T, g₀⁻¹ * x * g₀ ∈ (S : Subgroup G) := by
    intro x hx
    have hxQ : x ∈ (Q : Subgroup G) := hTQ hx
    rw [← hg₀, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨s, hs, rfl⟩ := hxQ
    simpa [MulAut.conj_apply, mul_assoc] using hs
  refine ⟨g₀⁻¹, ?_, ?_⟩
  ·
    intro x hx
    rw [mem_conjSub, inv_inv]
    have h := hUcl x hx.1 g₀ (hTS x (hUHT hx))
    simpa [mul_assoc] using h
  ·
    have hTmax : conjSub g₀⁻¹ (S : Subgroup G) ⊓ H = T := by
      refine hTH.2.2 _ inf_le_right ((S.isPGroup'.map _).to_le inf_le_left)
        (le_inf (fun x hx => ?_) hTH.1)
      rw [mem_conjSub, inv_inv]
      exact hTS x hx
    have hAT : conjSub g₀⁻¹ U ⊓ H ≤ T := by
      rw [← hTmax]
      exact inf_le_inf_right H (Subgroup.map_mono hUS)
    have hAab : IsMulCommutative (conjSub g₀⁻¹ U ⊓ H : Subgroup G) :=
      PropHSetup.isMulCommutative_of_le (isMulCommutative_map hUab _) inf_le_left
    have hcl : IsStronglyClosedIn (conjSub g₀⁻¹ U ⊓ H) T H := by
      intro a ha h hh hhT
      refine Subgroup.mem_inf.2 ⟨?_, H.mul_mem (H.mul_mem (H.inv_mem hh) ha.2) hh⟩
      have ha' : g₀⁻¹ * a * g₀ ∈ U := by simpa [mem_conjSub] using ha.1
      have h1 := hUcl _ ha' (g₀⁻¹ * h * g₀) (by
        have := hTS _ hhT
        simpa [mul_assoc] using this)
      rw [mem_conjSub, inv_inv]
      simpa [mul_assoc] using h1
    have hHlt : Nat.card H < Nat.card G := by
      rw [← Subgroup.card_top (G := G)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hH)
    exact isSStarIn_of_lt hIH hHlt hTH hAT hAab hcl

end CFSG.Goldschmidt
