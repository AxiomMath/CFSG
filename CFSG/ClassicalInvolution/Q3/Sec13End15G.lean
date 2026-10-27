module

public import CFSG.ClassicalInvolution.Q3.Sec13End15C
public import CFSG.ClassicalInvolution.Q3.Sec13End15F

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

private theorem e15g_zmod2_eq {x y : ZMod 2} (h : x = 0 ↔ y = 0) : x = y := by
  revert x y
  decide

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem mem_zSet_iff (h : EndHyp Ω) (s : TwinSit Ω K K' z) {a : G} :
    a ∈ zSet Ω ↔ ∃ g : G, a = g * z * g⁻¹ := by
  constructor
  · rintro ⟨L, hL, ha⟩
    obtain ⟨g, rfl⟩ := h.thmD.trans K s.mem L hL
    exact ⟨g, ((s.isInv.conj g).eq ha).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨conjSub g K, h.thmD.hyp.conjInvariant g K s.mem, s.isInv.conj g⟩

theorem polarE_map_eq_eGroup [hh : Fact (EndHyp Ω)] [h9 : Fact (Perp9 Ω)]
    (s : TwinSit Ω K K' z) {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf)
    {M : Subgroup G} (hM : M ∈ Ω) {p : zGroup Ω} (hp : IsUniqueInvolution M p.1) :
    (Polar.polarE bf (zPoints Ω) p).map (zGroup Ω).subtype = eGroup Ω M := by
  have h := hh.out
  have h9' := h9.out
  unfold Polar.polarE
  apply le_antisymm
  · refine Subgroup.map_le_iff_le_comap.mpr ((Subgroup.closure_le _).mpr ?_)
    rintro x ⟨hxS, hpx⟩
    have hxS' : x.1 ∈ zSet Ω := hxS
    obtain ⟨L, hL, hLx⟩ := hxS'
    have hxN : x.1 ∈ Subgroup.normalizer (M : Set G) :=
      (hbf.spec M hM p hp x).mp ((hbf.symm x p).trans hpx)
    exact h.mem_eGroup_of_normalizes h9' hM hL hLx hxN
  · unfold eGroup
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨J, hJ, hu⟩
    have hJΩ : J ∈ Ω := by
      rcases hJ with hJM | hJ'
      · rw [hJM]
        exact hM
      · exact hJ'.1
    have huD : u ∈ zGroup Ω := Subgroup.subset_closure ⟨J, hJΩ, hu⟩
    have huE : u ∈ eGroup Ω M := Subgroup.subset_closure ⟨J, hJ, hu⟩
    have huN : u ∈ Subgroup.normalizer (M : Set G) := h.eGroup_le_normalizer hM huE
    have hbfu : bf p ⟨u, huD⟩ = 0 :=
      (hbf.symm p ⟨u, huD⟩).trans ((hbf.spec M hM p hp ⟨u, huD⟩).mpr huN)
    have hT : (⟨u, huD⟩ : zGroup Ω) ∈ {x : zGroup Ω | x ∈ zPoints Ω ∧ bf p x = 0} :=
      ⟨⟨J, hJΩ, hu⟩, hbfu⟩
    exact Subgroup.mem_map_of_mem (zGroup Ω).subtype (Subgroup.subset_closure hT)

theorem not_isotropic_eGroup [hh : Fact (EndHyp Ω)] [h9 : Fact (Perp9 Ω)] (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K')
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) :
    ¬ ∀ x y : zGroup Ω, x.1 ∈ eGroup Ω K → y.1 ∈ eGroup Ω K → bf x y = 0 := by
  intro hiso
  have h := hh.out
  have h9' := h9.out
  have step : ∀ R R' : Subgroup G, R ∈ Ω → R' ∈ omegaStarNbr Ω R →
      eGroup Ω R = eGroup Ω K → eGroup Ω R' = eGroup Ω K := by
    intro R R' hR hR' hER
    have hR'Ω : R' ∈ Ω := hR'.1
    obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hR'Ω
    have htE : t ∈ eGroup Ω K := by
      rw [← hER]
      exact h.mem_eGroup_of_mem_omegaStarNbr hR' ht
    have hjD : t ∈ zGroup Ω := h.eGroup_le_zGroup s.mem htE
    have hEsub : eGroup Ω K ≤ eGroup Ω R' := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact (eGroup Ω R').one_mem
      · have hxD : x ∈ zGroup Ω := h.eGroup_le_zGroup s.mem hx
        have hbx : bf ⟨x, hxD⟩ ⟨t, hjD⟩ = 0 := hiso ⟨x, hxD⟩ ⟨t, hjD⟩ hx htE
        have hxN : x ∈ Subgroup.normalizer (R' : Set G) :=
          (hbf.spec R' hR'Ω ⟨t, hjD⟩ ht ⟨x, hxD⟩).mp hbx
        obtain ⟨g, hg⟩ := h.exists_conj_of_mem_eGroup_of_le h9' s h13 hE hx hx1
        have hxsz : IsUniqueInvolution (conjSub g K) x := by
          rw [hg]
          exact s.isInv.conj g
        exact h.mem_eGroup_of_normalizes h9' hR'Ω (h.thmD.hyp.conjInvariant g K s.mem) hxsz hxN
    have hcard : Nat.card (eGroup Ω R') = Nat.card (eGroup Ω K) :=
      h.card_eGroup_eq hR'Ω s.mem
    exact (Subgroup.eq_of_le_of_card_ge hEsub hcard.le).symm
  have key : ∀ L, Relation.ReflTransGen (dstarAdj Ω) K L → L ∈ Ω ∧ eGroup Ω L = eGroup Ω K := by
    intro L hL
    induction hL with
    | refl => exact ⟨s.mem, rfl⟩
    | @tail b c hb hbc ih =>
      obtain ⟨hbΩ, heb⟩ := ih
      refine ⟨hbc.1, ?_⟩
      rcases hbc.2 with hc | hc
      · exact step b c hbΩ hc heb
      · exact step b c hbΩ (Q3T6.Mu.omegaStarNbr_symm h.thmD.hyp hbc.1 hbΩ hc) heb
  have hle : zGroup Ω ≤ eGroup Ω K := by
    unfold zGroup
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨L, hL, hu⟩
    obtain ⟨-, heq⟩ := key L (h.star K s.mem L hL)
    have hu' := h.mem_eGroup_of_isUniqueInvolution hu
    rw [heq] at hu'
    exact hu'
  exact h13 (le_antisymm hle (h.eGroup_le_zGroup s.mem))

theorem polarData [hh : Fact (EndHyp Ω)] [h9 : Fact (Perp9 Ω)] (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K')
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) :
    Polar.PolarData bf (zPoints Ω) := by
  have h := hh.out
  have h9' := h9.out
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, s.mem, s.isInv⟩
  have hcardK : Nat.card (eGroup Ω K) = 8 :=
    (eGroup_eq_zGroup_inf_sup_of_le h h9' s h13 hE).1
  have hinj : Function.Injective (zGroup Ω).subtype := Subgroup.subtype_injective _
  have hgen : ∀ u ∈ zSet Ω, u ∈ (Subgroup.closure (zPoints Ω)).map (zGroup Ω).subtype := by
    intro u hu
    have huD : u ∈ zGroup Ω := Subgroup.subset_closure hu
    exact Subgroup.mem_map_of_mem _
      (Subgroup.subset_closure (show (⟨u, huD⟩ : zGroup Ω) ∈ zPoints Ω from hu))
  have hle : zGroup Ω ≤ (Subgroup.closure (zPoints Ω)).map (zGroup Ω).subtype :=
    (Subgroup.closure_le _).mpr (fun u hu => hgen u hu)
  refine ⟨?_, ⟨⟨z, hzD⟩, ⟨K, s.mem, s.isInv⟩⟩, ?_, ?_, ?_, ?_⟩
  ·
    rintro ⟨L, -, hu⟩
    exact hu.ne_one rfl
  ·
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle x.2)
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    exact hy
  ·
    rintro p ⟨M, hM, hp⟩
    have e1 := Subgroup.card_map_of_injective (K := Polar.polarE bf (zPoints Ω) p) hinj
    have e2 := congrArg (fun X : Subgroup G => Nat.card X) (polarE_map_eq_eGroup s hbf hM hp)
    exact e1.symm.trans (e2.trans ((h.card_eGroup_eq hM s.mem).trans hcardK))
  ·
    rintro p ⟨M, hM, hp⟩ x hx hx1
    obtain ⟨g₀, rfl⟩ := h.thmD.trans K s.mem M hM
    have hxE : x.1 ∈ eGroup Ω (conjSub g₀ K) := by
      rw [← polarE_map_eq_eGroup s hbf hM hp]
      exact Subgroup.mem_map_of_mem _ hx
    rw [h.eGroup_conj s.mem g₀, mem_conjSub_iff] at hxE
    have hne : g₀⁻¹ * x.1 * g₀ ≠ 1 := by
      intro h1
      apply hx1
      have e1 : x.1 = g₀ * (g₀⁻¹ * x.1 * g₀) * g₀⁻¹ := by group
      rw [h1, mul_one, mul_inv_cancel] at e1
      exact Subtype.ext e1
    obtain ⟨g, hg⟩ := h.exists_conj_of_mem_eGroup_of_le h9' s h13 hE hxE hne
    have hx_eq : x.1 = (g₀ * g) * z * (g₀ * g)⁻¹ := by
      calc x.1 = g₀ * (g₀⁻¹ * x.1 * g₀) * g₀⁻¹ := by group
        _ = g₀ * (g * z * g⁻¹) * g₀⁻¹ := by rw [hg]
        _ = (g₀ * g) * z * (g₀ * g)⁻¹ := by group
    refine ⟨conjSub (g₀ * g) K, h.thmD.hyp.conjInvariant _ K s.mem, ?_⟩
    rw [hx_eq]
    exact s.isInv.conj (g₀ * g)
  ·
    rintro p ⟨M, hM, hp⟩
    obtain ⟨g₀, rfl⟩ := h.thmD.trans K s.mem M hM
    by_contra hcon
    push Not at hcon
    apply not_isotropic_eGroup s h13 hE hbf
    intro x y hx hy
    have hPolar : ∀ u : G, u ∈ eGroup Ω (conjSub g₀ K) →
        ∃ w ∈ Polar.polarE bf (zPoints Ω) p, w.1 = u := by
      intro u hu
      have hmem : u ∈ (Polar.polarE bf (zPoints Ω) p).map (zGroup Ω).subtype := by
        rw [polarE_map_eq_eGroup s hbf hM hp]
        exact hu
      exact Subgroup.mem_map.mp hmem
    have hxu : g₀ * x.1 * g₀⁻¹ ∈ eGroup Ω (conjSub g₀ K) := by
      rw [h.eGroup_conj s.mem g₀]
      exact conj_mem_conjSub hx
    have hyu : g₀ * y.1 * g₀⁻¹ ∈ eGroup Ω (conjSub g₀ K) := by
      rw [h.eGroup_conj s.mem g₀]
      exact conj_mem_conjSub hy
    obtain ⟨x', hx', hx'1⟩ := hPolar _ hxu
    obtain ⟨y', hy', hy'1⟩ := hPolar _ hyu
    exact (hbf.conj g₀ x y x' y' hx'1 hy'1).symm.trans (hcon x' hx' y' hy')

theorem natCard_zGroup_eq_sixteen_local (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') :
    Nat.card (zGroup Ω) = 16 ∧ (∀ a ∈ zGroup Ω, a ≠ 1 → ∃ g : G, a = g * z * g⁻¹) ∧
      zGroup Ω ⊓ Subgroup.normalizer (K : Set G) = eGroup Ω K := by
  haveI : Fact (EndHyp Ω) := ⟨h⟩
  haveI : Fact (Perp9 Ω) := ⟨h9⟩
  obtain ⟨bf, hbf⟩ := h.exists_endForm h9 s h13
  obtain ⟨hcard, hpts⟩ :=
    Polar.PolarData.card_eq_sixteen hbf.sympForm (polarData s h13 hE hbf)
  have hmem : ∀ a ∈ zGroup Ω, a ≠ 1 → ∃ g : G, a = g * z * g⁻¹ := by
    intro a ha ha1
    have hx : a ∈ zSet Ω := hpts ⟨a, ha⟩ (fun e => ha1 (congrArg Subtype.val e))
    exact (h.mem_zSet_iff s).mp hx
  refine ⟨hcard, hmem, ?_⟩
  have hdiv := h.natCard_zGroup_eq_two_mul h9 s h13
  have hcardI : Nat.card ↥(zGroup Ω ⊓ Subgroup.normalizer (K : Set G)) = 8 := by omega
  have hle : eGroup Ω K ≤ zGroup Ω ⊓ Subgroup.normalizer (K : Set G) :=
    le_inf (h.eGroup_le_zGroup s.mem) (h.eGroup_le_normalizer s.mem)
  have hcardE : Nat.card (eGroup Ω K) = 8 :=
    (eGroup_eq_zGroup_inf_sup_of_le h h9 s h13 hE).1
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem inf_normalizer_eq_eGroup_local (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') {M : Subgroup G} (hM : M ∈ Ω) :
    zGroup Ω ⊓ Subgroup.normalizer (M : Set G) = eGroup Ω M := by
  obtain ⟨g, rfl⟩ := h.thmD.trans K s.mem M hM
  have hD : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hfwd : ∀ y : G, y ∈ zGroup Ω → g⁻¹ * y * g ∈ zGroup Ω := by
    intro y hy
    have := hD.conj_mem y hy g⁻¹
    rwa [inv_inv] at this
  have hbwd : ∀ y : G, g⁻¹ * y * g ∈ zGroup Ω → y ∈ zGroup Ω := by
    intro y hy
    have := hD.conj_mem _ hy g
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this
  rw [h.eGroup_conj s.mem g, ← (h.natCard_zGroup_eq_sixteen_local h9 s h13 hE).2.2]
  ext x
  rw [Subgroup.mem_inf, mem_conjSub_iff, Subgroup.mem_inf, mem_normalizer_conjSub_iff]
  exact ⟨fun ⟨hx, hN⟩ => ⟨hfwd x hx, hN⟩, fun ⟨hx, hN⟩ => ⟨hbwd x hx, hN⟩⟩

theorem eGroup_eq_iff_local (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') {M M' : Subgroup G} (hM : M ∈ Ω)
    (hM' : M' ∈ Ω) {b b' : G} (hb : IsUniqueInvolution M b) (hb' : IsUniqueInvolution M' b') :
    eGroup Ω M = eGroup Ω M' ↔ b = b' := by
  constructor
  · intro hEq
    obtain ⟨bf, hbf⟩ := h.exists_endForm h9 s h13
    have hbD : b ∈ zGroup Ω := Subgroup.subset_closure ⟨M, hM, hb⟩
    have hb'D : b' ∈ zGroup Ω := Subgroup.subset_closure ⟨M', hM', hb'⟩
    have hN : ∀ c : G, c ∈ zGroup Ω →
        (c ∈ Subgroup.normalizer (M : Set G) ↔ c ∈ Subgroup.normalizer (M' : Set G)) := by
      intro c hc
      have h1 := h.inf_normalizer_eq_eGroup_local h9 s h13 hE hM
      have h2 := h.inf_normalizer_eq_eGroup_local h9 s h13 hE hM'
      constructor
      · intro hcN
        have hmem : c ∈ zGroup Ω ⊓ Subgroup.normalizer (M : Set G) :=
          Subgroup.mem_inf.mpr ⟨hc, hcN⟩
        rw [h1, hEq, ← h2] at hmem
        exact (Subgroup.mem_inf.mp hmem).2
      · intro hcN
        have hmem : c ∈ zGroup Ω ⊓ Subgroup.normalizer (M' : Set G) :=
          Subgroup.mem_inf.mpr ⟨hc, hcN⟩
        rw [h2, ← hEq, ← h1] at hmem
        exact (Subgroup.mem_inf.mp hmem).2
    have hfa : (⟨b, hbD⟩ : zGroup Ω) = ⟨b', hb'D⟩ := by
      apply hbf.eq_of_forall_eq
      intro c
      apply e15g_zmod2_eq
      rw [hbf.spec M hM ⟨b, hbD⟩ hb c, hbf.spec M' hM' ⟨b', hb'D⟩ hb' c]
      exact hN c.1 c.2
    exact congrArg Subtype.val hfa
  · rintro rfl
    exact (h.eGroup_eq_of_mem_twinSet hM ⟨hM', b, hb, hb'⟩).symm

theorem eGroup_ne_of_local (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') {J : Subgroup G}
    (hJ : J ∈ omegaStarNbr Ω K) (hJt : J ∉ twinSet Ω K) : eGroup Ω J ≠ eGroup Ω K := by
  intro hEq
  obtain ⟨b, hb⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hJ.1
  have hbz : b = z := (h.eGroup_eq_iff_local h9 s h13 hE hJ.1 s.mem hb s.isInv).mp hEq
  exact hJt ⟨hJ.1, z, s.isInv, by rw [← hbz]; exact hb⟩

theorem exists_transitive_pair_of_local (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') :
    ∃ A : Subgroup G, A ≤ zGroup Ω ∧ eGroup Ω K ≤ A ∧ Nat.card A = 16 ∧
      ∃ Λ : Subgroup G, Λ ≤ Subgroup.normalizer (A : Set G) ∧
        ∀ a ∈ A, a ≠ 1 → ∃ l ∈ Λ, a = l * z * l⁻¹ := by
  obtain ⟨h16, hpts, -⟩ := h.natCard_zGroup_eq_sixteen_local h9 s h13 hE
  haveI : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  refine ⟨zGroup Ω, le_rfl, h.eGroup_le_zGroup s.mem, h16, ⊤, ?_, ?_⟩
  · exact le_of_eq (Subgroup.normalizer_eq_top (zGroup Ω : Subgroup G)).symm
  · intro a ha ha1
    obtain ⟨g, hg⟩ := hpts a ha ha1
    exact ⟨g, Subgroup.mem_top g, hg⟩

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
