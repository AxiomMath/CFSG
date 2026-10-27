module

public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Norm

public section

namespace CFSG.GH74.GLS.Th2.P85.Sp

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.TwoThin
open CFSG.GH74.GLS.C3.Layer1.Bk.J2C
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreOf_le_M_of_plane {D M Q : Subgroup G}
    (hQnorm : Q ≤ normalizer (pPrimeCoreOf 2 D : Set G)) (hQcard : Nat.card ↥Q = 4)
    (hQpow : ∀ q : ↥Q, q ^ 2 = 1) (hQM : ∀ q ∈ Q, q ≠ 1 → centralizer ({q} : Set G) ≤ M) :
    pPrimeCoreOf 2 D ≤ M := by
  have hKodd : ¬ 2 ∣ Nat.card ↥(pPrimeCoreOf 2 D) := by
    have hodd := TwoThin.card_pPrimeCoreOf_odd D
    rw [Nat.odd_iff] at hodd
    omega
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    2 Nat.prime_two Q (pPrimeCoreOf 2 D) (fun q => hQpow q) hQcard hKodd hQnorm
  rw [hgen]
  exact iSup_le fun q => iSup_le fun hq =>
    inf_le_right.trans (hQM q q.2 (fun h => hq (Subtype.ext h)))

omit [Finite G] in
theorem v_mem_cent (v : G) : v ∈ centralizer ({v} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 rfl

omit [Finite G] in
theorem pPrimeCoreOf_cent_le (v : G) :
    pPrimeCoreOf 2 (centralizer ({v} : Set G)) ≤ centralizer ({v} : Set G) :=
  TwoThin.pPrimeCoreOf_le _

omit [Finite G] in
theorem mem_normalizer_pPrimeCoreOf_cent {v c : G} (hc : c ∈ centralizer ({v} : Set G)) :
    c ∈ normalizer (pPrimeCoreOf 2 (centralizer ({v} : Set G)) : Set G) :=
  TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hc)

omit [Finite G] in
theorem imgM_preimgM (M : Subgroup G) (Lb : Subgroup (Mb M)) : imgM M (preimgM M Lb) = Lb := by
  apply le_antisymm
  · intro y hy
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hy
    obtain ⟨hmM, hmL⟩ := mem_preimgM_iff.1 hm
    exact hmL
  · intro y hy
    obtain ⟨m, rfl⟩ := barMk_surjective y
    exact mem_imgM_iff.2 ⟨m, mem_preimgM_iff.2 ⟨m.2, hy⟩, rfl⟩


namespace P89Std

variable {M W Q : Subgroup G} {v : G} {Ebar : Subgroup (Mb M)}
variable (h : P89Std M W Q v Ebar)
include h

omit [Finite G] in
theorem W_le_C : W ≤ centralizer ({v} : Set G) := fun w hw =>
  Subgroup.mem_centralizer_singleton_iff.2 (h.v_cent w hw).symm

theorem U1_le_M : pPrimeCoreOf 2 (centralizer ({v} : Set G)) ≤ M := by
  refine pPrimeCoreOf_le_M_of_plane ?_ h.Q_card h.Q_pow h.Q_cent
  intro q hq
  exact TwoThin.mem_normalizer_pPrimeCoreOf
    (Subgroup.le_normalizer (h.W_le_C (h.Q_le hq)))


theorem U1_le_R : pPrimeCoreOf 2 (centralizer ({v} : Set G)) ≤ pPrimeCoreOf 2 M := by
  have hU1M := h.U1_le_M
  have hU1C := pPrimeCoreOf_cent_le v
  intro u hu
  have huM : u ∈ M := hU1M hu
  have hOC : ∀ x ∈ imgM M (pPrimeCoreOf 2 (centralizer ({v} : Set G))),
      x ∈ centralizer ({h.vb} : Set (Mb M)) := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hx
    have hmv : (m : G) * v = v * m := Subgroup.mem_centralizer_singleton_iff.1 (hU1C hm)
    rw [Subgroup.mem_centralizer_singleton_iff]
    show barMk ↥M m * barMk ↥M ⟨v, h.v_mem_M⟩ = barMk ↥M ⟨v, h.v_mem_M⟩ * barMk ↥M m
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hmv
  have hOn : ∀ y ∈ centralizer ({h.vb} : Set (Mb M)),
      ∀ x ∈ imgM M (pPrimeCoreOf 2 (centralizer ({v} : Set G))),
        y * x * y⁻¹ ∈ imgM M (pPrimeCoreOf 2 (centralizer ({v} : Set G))) := by
    intro y hy x hx
    rw [← h.imgM_N0] at hy
    obtain ⟨c, hc, rfl⟩ := mem_imgM_iff.1 hy
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hx
    obtain ⟨hcN, hcM⟩ := Subgroup.mem_inf.1 hc
    have hcC := h.normalizer_W0_le_cent hcN
    have hn := (Subgroup.mem_normalizer_iff.1 (mem_normalizer_pPrimeCoreOf_cent hcC)) m
    have hmem : (c : G) * m * (c : G)⁻¹ ∈ pPrimeCoreOf 2 (centralizer ({v} : Set G)) := hn.1 hm
    have hM : (c : G) * m * (c : G)⁻¹ ∈ M := M.mul_mem (M.mul_mem c.2 m.2) (M.inv_mem c.2)
    refine mem_imgM_iff.2 ⟨⟨(c : G) * m * (c : G)⁻¹, hM⟩, hmem, ?_⟩
    have h1 : (⟨(c : G) * m * (c : G)⁻¹, hM⟩ : ↥M) = c * m * c⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
  have hOodd : Odd (Nat.card ↥(imgM M (pPrimeCoreOf 2 (centralizer ({v} : Set G))))) := by
    have hdvd := Subgroup.card_dvd_of_surjective (f := toImgM hU1M) (toImgM_surjective hU1M)
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd (centralizer ({v} : Set G))) hdvd
  have hEcomm : ∀ x ∈ imgM M (pPrimeCoreOf 2 (centralizer ({v} : Set G))), ∀ e ∈ Ebar,
      x * e = e * x := by
    intro x hx e he
    have hxC := hOC x hx
    have heC : e ∈ centralizer ({h.vb} : Set (Mb M)) := h.facts.E_le he
    have h1 : x * e * x⁻¹ ∈ Ebar := h.facts.E_normal x hxC e he
    have h2 : e * x * e⁻¹ ∈ imgM M (pPrimeCoreOf 2 (centralizer ({v} : Set G))) := hOn e heC x hx
    have h3 : x * e * x⁻¹ * e⁻¹ ∈ Ebar := Ebar.mul_mem h1 (Ebar.inv_mem he)
    have h4 : x * e * x⁻¹ * e⁻¹ ∈ imgM M (pPrimeCoreOf 2 (centralizer ({v} : Set G))) := by
      have h5 : x * (e * x⁻¹ * e⁻¹) = x * e * x⁻¹ * e⁻¹ := by group
      rw [← h5]
      refine Subgroup.mul_mem _ hx ?_
      have h6 : e * x⁻¹ * e⁻¹ = (e * x * e⁻¹)⁻¹ := by group
      rw [h6]
      exact Subgroup.inv_mem _ h2
    have h7 : x * e * x⁻¹ * e⁻¹ = 1 := by
      set g := x * e * x⁻¹ * e⁻¹ with hg
      have hd1 : orderOf g ∣ 32 := by
        rw [← h.facts.card_E]
        exact Subgroup.orderOf_dvd_natCard Ebar h3
      have hd2 : orderOf g ∣ Nat.card ↥(imgM M (pPrimeCoreOf 2 (centralizer ({v} : Set G)))) :=
        Subgroup.orderOf_dvd_natCard _ h4
      have hcop : Nat.Coprime 32 (Nat.card ↥(imgM M (pPrimeCoreOf 2 (centralizer ({v} : Set G))))) :=
        Nat.Coprime.pow_left 5 ((Nat.coprime_two_left).2 hOodd)
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
    have h8 : x * e * x⁻¹ = e := by
      have := congrArg (fun t => t * e) h7
      simpa [mul_assoc] using this
    calc x * e = x * e * x⁻¹ * x := by group
      _ = e * x := by rw [h8]
  have hO1 : ∀ x ∈ imgM M (pPrimeCoreOf 2 (centralizer ({v} : Set G))), x = 1 := by
    intro x hx
    rcases h.facts.cent_E x (hOC x hx) (hEcomm x hx) with h1 | h1
    · exact h1
    · exfalso
      have hv2 : 2 ∣ Nat.card ↥(imgM M (pPrimeCoreOf 2 (centralizer ({v} : Set G)))) := by
        have := Subgroup.orderOf_dvd_natCard _ hx
        rwa [h1, h.vb_two] at this
      exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 hv2)
  have hu1 : barMk ↥M ⟨u, huM⟩ = 1 := hO1 _ (mem_imgM_iff.2 ⟨⟨u, huM⟩, hu, rfl⟩)
  exact (barMk_eq_one_iff_mem_pPrimeCoreOf _).1 hu1


theorem card_normal_two_le (hnot : ¬ centralizer ({v} : Set G) ≤ M)
    (N : Subgroup (Mb (centralizer ({v} : Set G)))) (hNn : N.Normal) (hN2 : IsPGroup 2 ↥N)
    (hz : barMk ↥(centralizer ({v} : Set G)) ⟨v, v_mem_cent v⟩ ∈ N) : Nat.card ↥N ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hN2.exists_card_eq
  obtain ⟨V, hV⟩ : ∃ V : Subgroup G, V = preimgM (centralizer ({v} : Set G)) N := ⟨_, rfl⟩
  have hVC : V ≤ centralizer ({v} : Set G) := by
    rw [hV]
    exact preimgM_le
  have hVn : ∀ c ∈ centralizer ({v} : Set G), ∀ g ∈ V, c * g * c⁻¹ ∈ V := by
    rw [hV]
    exact preimgM_normal (M := centralizer ({v} : Set G)) (Lb := N)
      (fun n x hx => hNn.conj_mem x hx n)
  have hU1V : pPrimeCoreOf 2 (centralizer ({v} : Set G)) ≤ V := by
    intro u hu
    have huC : u ∈ centralizer ({v} : Set G) := pPrimeCoreOf_cent_le v hu
    rw [hV]
    refine mem_preimgM_iff.2 ⟨huC, ?_⟩
    have : barMk ↥(centralizer ({v} : Set G)) ⟨u, huC⟩ = 1 :=
      (barMk_eq_one_iff_mem_pPrimeCoreOf _).2 hu
    rw [this]
    exact N.one_mem
  have hvV : v ∈ V := by
    rw [hV]
    exact mem_preimgM_iff.2 ⟨v_mem_cent v, hz⟩
  have hVnorm : centralizer ({v} : Set G) ≤ normalizer (V : Set G) := fun c hc =>
    CFSG.GH74.Generic.S45.EvSpor.mem_normalizer_of_conj_le (hVn c hc)
  have hcardV : Nat.card ↥V =
      Nat.card ↥N * Nat.card ↥(pPrimeCoreOf 2 (centralizer ({v} : Set G))) := by
    rw [card_eq_card_imgM_mul (M := centralizer ({v} : Set G)) hVC, hV, imgM_preimgM,
      inf_eq_right.2 (hV ▸ hU1V)]
  have hU1odd : Odd (Nat.card ↥(pPrimeCoreOf 2 (centralizer ({v} : Set G)))) :=
    TwoThin.card_pPrimeCoreOf_odd _
  have hfactV : (Nat.card ↥V).factorization 2 = k := by
    rw [hcardV, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      C3.Layer1.Back.Setup91.factorization_two_of_odd hU1odd, hk,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hWC : IsSylowOf 2 W (centralizer ({v} : Set G)) := h.W_syl.of_le h.W_le_C le_top
  have hWV : IsSylowOf 2 (W ⊓ V) V := hWC.inf_of_le_normalizer hVC hVnorm
  have hcardWV : Nat.card ↥(W ⊓ V) = Nat.card ↥N := by
    rw [hWV.card_eq, hfactV, hk]
  have hRodd : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := TwoThin.card_pPrimeCoreOf_odd M
  obtain ⟨V0, hV0⟩ : ∃ V0 : Subgroup G, V0 = V ⊓ M := ⟨_, rfl⟩
  have hV0M : V0 ≤ M := hV0 ▸ inf_le_right
  have hV0V : V0 ≤ V := hV0 ▸ inf_le_left
  have hWV0 : W ⊓ V = W ⊓ V0 := by
    ext x
    rw [hV0, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxW, hxV⟩
      exact ⟨hxW, hxV, h.W_le hxW⟩
    · rintro ⟨hxW, hxV, -⟩
      exact ⟨hxW, hxV⟩
  have hU1R := h.U1_le_R
  have hU1M := h.U1_le_M
  have hmemV0 : ∀ m : ↥M, (m : G) ∈ V0 ↔ (m : G) ∈ V := fun m => by
    rw [hV0, Subgroup.mem_inf]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', m.2⟩⟩
  have hVmC : ∀ y ∈ imgM M V0, y ∈ centralizer ({h.vb} : Set (Mb M)) := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hy
    have hmv : (m : G) * v = v * m := Subgroup.mem_centralizer_singleton_iff.1 (hVC (hV0V hm))
    rw [Subgroup.mem_centralizer_singleton_iff]
    show barMk ↥M m * barMk ↥M ⟨v, h.v_mem_M⟩ = barMk ↥M ⟨v, h.v_mem_M⟩ * barMk ↥M m
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hmv
  have hVmn : ∀ y ∈ centralizer ({h.vb} : Set (Mb M)), ∀ x ∈ imgM M V0, y * x * y⁻¹ ∈ imgM M V0 := by
    intro y hy x hx
    rw [← h.imgM_N0] at hy
    obtain ⟨c, hc, rfl⟩ := mem_imgM_iff.1 hy
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hx
    obtain ⟨hcN, hcM⟩ := Subgroup.mem_inf.1 hc
    have hcC := h.normalizer_W0_le_cent hcN
    have hmV : (c : G) * m * (c : G)⁻¹ ∈ V := hVn _ hcC _ (hV0V hm)
    have hM : (c : G) * m * (c : G)⁻¹ ∈ M := M.mul_mem (M.mul_mem c.2 m.2) (M.inv_mem c.2)
    refine mem_imgM_iff.2 ⟨⟨(c : G) * m * (c : G)⁻¹, hM⟩, (hmemV0 ⟨_, hM⟩).2 hmV, ?_⟩
    have h1 : (⟨(c : G) * m * (c : G)⁻¹, hM⟩ : ↥M) = c * m * c⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
  have hVm2 : IsPGroup 2 ↥(imgM M V0) := by
    intro y
    obtain ⟨m, hm, hmy⟩ := mem_imgM_iff.1 y.2
    have hmV : (m : G) ∈ V := hV0V hm
    rw [hV] at hmV
    obtain ⟨hmC, hmN⟩ := mem_preimgM_iff.1 hmV
    obtain ⟨j, hj⟩ := hN2 ⟨_, hmN⟩
    refine ⟨j, Subtype.ext ?_⟩
    have hj' : (barMk ↥(centralizer ({v} : Set G)) ⟨m, hmC⟩) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hmem : (⟨m, hmC⟩ : ↥(centralizer ({v} : Set G))) ^ 2 ^ j ∈ pPrimeCore 2 ↥(centralizer ({v} : Set G)) := by
      rw [← ker_barMk, MonoidHom.mem_ker, map_pow]
      exact hj'
    have hpow : ((m : G) ^ 2 ^ j) ∈ pPrimeCoreOf 2 (centralizer ({v} : Set G)) :=
      Subgroup.mem_map.2 ⟨_, hmem, rfl⟩
    have h1 : barMk ↥M (m ^ 2 ^ j) = 1 :=
      (barMk_eq_one_iff_mem_pPrimeCoreOf _).2 (hU1R hpow)
    rw [map_pow] at h1
    show (y : Mb M) ^ 2 ^ j = 1
    rw [← hmy]
    exact h1
  have hvVm : h.vb ∈ imgM M V0 :=
    mem_imgM_iff.2 ⟨⟨v, h.v_mem_M⟩, (hmemV0 ⟨v, h.v_mem_M⟩).2 hvV, rfl⟩
  have hVmE : imgM M V0 ≤ Ebar := h.facts.two_core _ hVmC hVmn hVm2
  have hWC0 : IsSylowOf 2 W (centralizer ({v} : Set G) ⊓ M) :=
    h.W_syl.of_le (le_inf h.W_le_C h.W_le) le_top
  have hV0norm : centralizer ({v} : Set G) ⊓ M ≤ normalizer (V0 : Set G) := by
    intro c hc
    refine CFSG.GH74.Generic.S45.EvSpor.mem_normalizer_of_conj_le fun x hx => ?_
    have hxV := hV0V hx
    have hxM := hV0M hx
    rw [hV0, Subgroup.mem_inf]
    exact ⟨hVn c hc.1 x hxV, M.mul_mem (M.mul_mem hc.2 hxM) (M.inv_mem hc.2)⟩
  have hV0S : IsSylowOf 2 (W ⊓ V0) V0 :=
    hWC0.inf_of_le_normalizer (le_inf (hV0V.trans hVC) hV0M) hV0norm
  have hcardV0 : Nat.card ↥V0 =
      Nat.card ↥(imgM M V0) * Nat.card ↥(V0 ⊓ pPrimeCoreOf 2 M) := card_eq_card_imgM_mul hV0M
  have hV0Rodd : Odd (Nat.card ↥(V0 ⊓ pPrimeCoreOf 2 M)) :=
    Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨j, hj⟩ := hVm2.exists_card_eq
  have hfactV0 : (Nat.card ↥V0).factorization 2 = j := by
    rw [hcardV0, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      C3.Layer1.Back.Setup91.factorization_two_of_odd hV0Rodd, hj,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hcardWVm : Nat.card ↥(W ⊓ V) = Nat.card ↥(imgM M V0) := by
    rw [hWV0, hV0S.card_eq, hfactV0, hj]
  by_cases hex : ∃ x ∈ imgM M V0, x ≠ 1 ∧ x ≠ h.vb
  ·
    exfalso
    have hEVm : Ebar ≤ imgM M V0 := h.facts.irred _ hVmE hvVm hVmn hex
    have hVmEq : imgM M V0 = Ebar := le_antisymm hVmE hEVm
    have hcN : Nat.card ↥N = 32 := by
      rw [← hcardWV, hcardWVm, hVmEq, h.facts.card_E]
    have hWVle : W ⊓ V ≤ W0 M W Ebar := by
      rintro w ⟨hwW, hwV⟩
      have hwM : w ∈ M := h.W_le hwW
      refine mem_W0_iff.2 ⟨hwW, hwM, hVmE ?_⟩
      exact mem_imgM_iff.2 ⟨⟨w, hwM⟩, (hmemV0 ⟨w, hwM⟩).2 hwV, rfl⟩
    have hWVeq : W ⊓ V = W0 M W Ebar :=
      Subgroup.eq_of_le_of_card_ge hWVle (by rw [h.card_W0, hcardWV, hcN])
    have hW0V : W0 M W Ebar ≤ V := hWVeq ▸ inf_le_right
    have hcardW0 : Nat.card ↥(W0 M W Ebar) = 2 ^ (Nat.card ↥V).factorization 2 := by
      rw [hfactV, h.card_W0, ← hk, hcN]
    have hVeq : V0 = V := by
      refine Subgroup.eq_of_le_of_card_ge hV0V ?_
      have hU1V0 : pPrimeCoreOf 2 (centralizer ({v} : Set G)) ≤ V0 ⊓ pPrimeCoreOf 2 M :=
        le_inf (hV0 ▸ le_inf hU1V hU1M) hU1R
      have h1 := Subgroup.card_le_of_le hU1V0
      rw [hcardV, hcardV0, hVmEq, h.facts.card_E, hcN]
      exact Nat.mul_le_mul_left _ h1
    have hVM : V ≤ M := hVeq ▸ hV0M
    apply hnot
    intro c hc
    obtain ⟨l, hlV, hlc⟩ := CFSG.Walter.W67.Sec6.exists_mul_mem_normalizer_of_sylowIn (r := 2)
      hW0V hcardW0 (hVnorm hc)
    have hn : l * c ∈ M := h.normalizer_W0_le_M hlc
    have : c = l⁻¹ * (l * c) := by group
    rw [this]
    exact M.mul_mem (M.inv_mem (hVM hlV)) hn
  · push Not at hex
    have hle : imgM M V0 ≤ zpowers h.vb := fun x hx => by
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      · rw [hex x hx hx1]
        exact Subgroup.mem_zpowers _
    calc Nat.card ↥N = Nat.card ↥(W ⊓ V) := hcardWV.symm
      _ = Nat.card ↥(imgM M V0) := hcardWVm
      _ ≤ Nat.card ↥(zpowers h.vb) := Subgroup.card_le_of_le hle
      _ = 2 := by rw [Nat.card_zpowers, h.vb_two]

end P89Std

end CFSG.GH74.GLS.Th2.P85.Sp
