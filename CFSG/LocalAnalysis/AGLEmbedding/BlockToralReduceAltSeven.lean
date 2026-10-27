module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPLAux
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique BlockAltSevenPL

namespace ToralReduce

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mk_eq_one_iff {M : Subgroup G} {c : G} (hc : c ∈ M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨c, hc⟩ = 1 ↔ c ∈ pCoreOf 2 M := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨m, hm, hmc⟩
    rwa [show (⟨c, hc⟩ : ↥M) = m from Subtype.ext hmc.symm]

theorem center_eq_bot_of_mulEquiv_alt {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 7)) :
    Subgroup.center X = ⊥ := by
  have h := alternatingGroup.center_eq_bot (α := Fin 7) (by simp)
  rw [eq_bot_iff]
  intro z hz
  have : e z ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz g]
  rw [h, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot, ← map_eq_one_iff e e.injective]
  exact this

theorem inner_of_nineThreeFive {M S L : Subgroup G} (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (h5 : NineThreeFive M L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    (∀ (x : G) (hxM : x ∈ M), x ∈ Subgroup.normalizer (L : Set G) →
      ∃ l ∈ barM M L, l⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∧
    ∃ (s : G) (hsM : s ∈ M), s ∈ S ∧ QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨s, hsM⟩ ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨hsh, ⟨e⟩, hU⟩ := h5
  have hLc := hL.toIsTwoPrimeComponent
  set N := Subgroup.normalizer (L : Set G)
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hNU : N ≤ Subgroup.normalizer (blockU L : Set G) := fun _ hg =>
    QuasithinUnique.C1.mem_normalizer_blockU hg
  set ρ : ↥N →* MulAut ↥(blockU L) :=
    (blockU L).normalizerMonoidHom.comp (Subgroup.inclusion hNU)
  have hρ : ∀ (n : ↥N) (u : ↥(blockU L)), ((ρ n u : ↥(blockU L)) : G) = n * u * n⁻¹ :=
    fun _ _ => rfl
  obtain ⟨hΓ, hΓs⟩ := card_mulAut_eq_and_isSimpleGroup (W := ↥(blockU L))
    (fun a b => Subtype.ext (QuasithinUnique.C1.blockU_comm hsh a a.2 b
      (QuasithinUnique.C1.blockU_le_blockQ hsh b.2)))
    (fun a => Subtype.ext (QuasithinUnique.C1.blockU_sq hsh a a.2)) hU
  have : Finite (MulAut ↥(blockU L)) := Nat.finite_of_card_ne_zero (by rw [hΓ]; norm_num)
  have hρL : ∀ (l : G) (hl : l ∈ L), ρ ⟨l, hLN hl⟩ = 1 ↔ l ∈ pCoreOf 2 L := fun l hl =>
    conj_eq_one_iff_mem_pCoreOf hsh hρ (n := ⟨l, hLN hl⟩) hl
  have hπL : ∀ (l : G) (hl : l ∈ L),
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLc.le hl⟩ = 1 ↔ l ∈ pCoreOf 2 L := fun l hl => by
    rw [mk_eq_one_iff, ← hLc.inf_twoCore]
    exact ⟨fun h => ⟨hl, h⟩, fun h => h.2⟩
  set π : ↥L →* ↥M ⧸ CFSG.pCore 2 ↥M := (QuotientGroup.mk' _).comp (Subgroup.inclusion hLc.le)
  set ρL : ↥L →* MulAut ↥(blockU L) := ρ.comp (Subgroup.inclusion hLN)
  have hker : π.ker = ρL.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact (hπL l l.2).trans (hρL l l.2).symm
  set H := (L.subgroupOf N).map ρ
  obtain ⟨θ₀⟩ := nonempty_mulEquiv_range_of_ker_eq hker
  have hHr : ρL.range = H := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self L, ← Subgroup.map_map,
      map_inclusion_subgroupOf le_rfl hLN]
  have hπr : π.range = barM M L := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self L, barM, ← Subgroup.map_map,
      map_inclusion_subgroupOf le_rfl hLc.le]
  let θ : ↥H ≃* alternatingGroup (Fin 7) :=
    (MulEquiv.subgroupCongr hHr.symm).trans (θ₀.symm.trans ((MulEquiv.subgroupCongr hπr).trans e))
  have hH : Nat.card H = 2520 := by
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hNH : ∀ n : ↥N, ρ n ∈ H := fun n => by
    have hn : Subgroup.normalizer ((L.subgroupOf N : Subgroup ↥N) : Set ↥N) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_in_normalizer
    exact mem_of_mem_normalizer_of_index_eight hΓ hH
      (Subgroup.le_normalizer_map ρ ⟨n, by rw [hn]; trivial, rfl⟩)
  have key : ∀ (x : G) (hxM : x ∈ M) (hxN : x ∈ N), ∃ (l : G) (hl : l ∈ L),
      ρ ⟨l, hLN hl⟩ = ρ ⟨x, hxN⟩ ∧
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLc.le hl⟩)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro x hxM hxN
    obtain ⟨m, hm, hmx⟩ := hNH ⟨x, hxN⟩
    have hmL : (m : G) ∈ L := hm
    refine ⟨m, hmL, hmx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have hkL : (k : G) ∈ L := hk
    set y : G := (m : G)⁻¹ * x
    have hyN : y ∈ N := N.mul_mem (N.inv_mem m.2) hxN
    have hyM : y ∈ M := M.mul_mem (M.inv_mem (hLc.le hmL)) hxM
    have hρy : ρ ⟨y, hyN⟩ = 1 := by
      have : (⟨y, hyN⟩ : ↥N) = m⁻¹ * ⟨x, hxN⟩ := rfl
      rw [this, map_mul, map_inv, ← hmx, inv_mul_cancel]
    have hcL : y * k * y⁻¹ * (k : G)⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN k).mp hkL) (L.inv_mem hkL)
    have hρc : ρ ⟨y * k * y⁻¹ * (k : G)⁻¹, hLN hcL⟩ = 1 := by
      have : (⟨y * k * y⁻¹ * (k : G)⁻¹, hLN hcL⟩ : ↥N) =
          ⟨y, hyN⟩ * ⟨k, hLN hkL⟩ * ⟨y, hyN⟩⁻¹ * ⟨k, hLN hkL⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hρy]
      group
    have h1 := (hπL _ hcL).mpr ((hρL _ hcL).mp hρc)
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩ * QuotientGroup.mk' _ k *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩)⁻¹ * (QuotientGroup.mk' _ k)⁻¹ = 1 := by
      rw [← h1, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    have h3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G), hLc.le hmL⟩)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ =
          QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [h3]
    have h4 := mul_eq_one_iff_eq_inv.mp h2
    rw [inv_inv] at h4
    calc QuotientGroup.mk' _ k * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩ * QuotientGroup.mk' _ k *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩)⁻¹ *
            QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩ := by rw [h4]
      _ = _ := by group
  refine ⟨fun x hxM hxN => ?_, ?_⟩
  · obtain ⟨l, hl, -, hc⟩ := key x hxM hxN
    exact ⟨_, ⟨⟨l, hLc.le hl⟩, hl, rfl⟩, hc⟩
  ·
    obtain ⟨s, hs, hρs⟩ := exists_mem_conj_blockU_ne_one hA hL hsh hρ hSL
    refine ⟨s, hA.twoRadical.1 hs, hs, fun hsC => hρs ?_⟩
    obtain ⟨l, hl, hρl, hc⟩ := key s (hA.twoRadical.1 hs) (hSL hs)
    have hlC : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLc.le hl⟩ ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      have := (Subgroup.centralizer _).mul_mem hsC ((Subgroup.centralizer _).inv_mem hc)
      simpa using this
    have hlZ : (⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLc.le hl⟩, ⟨⟨l, hLc.le hl⟩, hl, rfl⟩⟩ :
        ↥(barM M L)) ∈ Subgroup.center ↥(barM M L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hlC g g.2)
    rw [center_eq_bot_of_mulEquiv_alt e, Subgroup.mem_bot] at hlZ
    have hl1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLc.le hl⟩ = 1 := congrArg Subtype.val hlZ
    rw [← hρl]
    exact (hρL l hl).mpr ((hπL l hl).mp hl1)

theorem isSolvable_of_card_dvd_seventyTwo {X : Type*} [Group X] [Finite X]
    (h : Nat.card X ∣ 72) : Group.IsSolvable X := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 (show Nat.card X ∣ 2 ^ 3 * 3 ^ 2 from h)
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
  have : Fintype X := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

theorem false_of_nineThreeFive (h86 : Asc81bEightSix) {M S L : Subgroup G}
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (h5 : NineThreeFive M L) {V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hVp : ⁅V, V⁆ = V)
    (hVL : V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hVS : V ≤ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {u : ↥M ⧸ CFSG.pCore 2 ↥M} (huC : u ∉ Subgroup.centralizer (barM M L : Set _))
    (huV : u ∈ V) : False := by
  have hLc := hL.toIsTwoPrimeComponent
  have hSbL := h86 G M S hK hA _ hLc.component
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := hLc.le_normalizer hSbL hA.twoRadical.1
  obtain ⟨hinner, s, hsM, hsS, hsC⟩ := inner_of_nineThreeFive hA hL h5 hSL
  obtain ⟨-, ⟨e⟩, -⟩ := h5
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set Lb := barM M L
  set Nb := Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  set c : ↥Nb →* MulAut ↥Lb := Lb.normalizerMonoidHom
  have hkerc : ∀ n : ↥Nb, c n = 1 ↔ (n : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
      Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun n => by
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  set cL : ↥Lb →* MulAut ↥Lb := c.comp (Subgroup.inclusion Subgroup.le_normalizer)
  have hZ := center_eq_bot_of_mulEquiv_alt e
  have hcL : Function.Injective cL := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 := (hkerc _).mp hl
    have : l ∈ Subgroup.center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h1 g g.2)
    rwa [hZ, Subgroup.mem_bot] at this
  have hrange : ∀ (x : G) (hxM : x ∈ M) (hxN : x ∈ Subgroup.normalizer (L : Set G))
      (hxNb : mk ⟨x, hxM⟩ ∈ Nb), c ⟨_, hxNb⟩ ∈ cL.range := by
    intro x hxM hxN hxNb
    obtain ⟨l, hl, hlx⟩ := hinner x hxM hxN
    have hlNb : l ∈ Nb := Subgroup.le_normalizer hl
    refine ⟨⟨l, hl⟩, ?_⟩
    have h1 : c (⟨l, hlNb⟩⁻¹ * ⟨_, hxNb⟩) = 1 := (hkerc _).mpr hlx
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  set A := cL.range
  let θ : ↥A ≃* alternatingGroup (Fin 7) := (MonoidHom.ofInjective hcL).symm.trans e
  set Vc := (V.subgroupOf Nb).map c
  set Sc := ((barM M S).subgroupOf Nb).map c
  have hVA : Vc ≤ A := by
    rintro _ ⟨⟨v, hvNb⟩, hv, rfl⟩
    obtain ⟨⟨m, hmM⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) v
    have hX : barM M ((V.comap mk).map M.subtype) ≤ Nb := by
      rw [barM, show ((V.comap mk).map M.subtype).subgroupOf M = V.comap mk from
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective _,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
      exact hVL
    have hmN := hLc.le_normalizer hX (Subgroup.map_subtype_le _) ⟨⟨m, hmM⟩, hv, rfl⟩
    exact hrange m hmM hmN hvNb
  have hSA : Sc ≤ A := by
    rintro _ ⟨⟨_, hsNb⟩, ⟨⟨t, htM⟩, ht, rfl⟩, rfl⟩
    exact hrange t htM (hSL ht) hsNb
  have hSb2 : IsPGroup 2 (barM M S) := hA.twoRadical.isPGroup.comap_subtype.map _
  have hSc2 : IsPGroup 2 Sc := (hSb2.comap_subtype (K := Nb)).map c
  have hSc1 : Sc ≠ ⊥ := by
    intro hbot
    have hmem : c ⟨mk ⟨s, hsM⟩, hSbL ⟨⟨s, hsM⟩, hsS, rfl⟩⟩ ∈ Sc :=
      ⟨_, Subgroup.mem_subgroupOf.mpr ⟨⟨s, hsM⟩, hsS, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, hkerc] at hmem
    exact hsC hmem
  have hVSc : Vc ≤ Subgroup.normalizer (Sc : Set (MulAut ↥Lb)) := by
    refine le_trans (Subgroup.map_mono fun n hn => ?_) (Subgroup.le_normalizer_map c)
    rw [← Subgroup.subgroupOf_normalizer_eq (hSbL)]
    exact Subgroup.mem_subgroupOf.mpr (hVS (Subgroup.mem_subgroupOf.mp hn))
  have h72 := card_dvd_seventyTwo_of_mulEquiv θ (T := Sc.subgroupOf A) (P := Vc.subgroupOf A)
    (hSc2.comap_subtype) (fun h => hSc1 ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hSA))
    (fun p hp => by
      rw [← Subgroup.subgroupOf_normalizer_eq hSA]
      exact Subgroup.mem_subgroupOf.mpr (hVSc (Subgroup.mem_subgroupOf.mp hp)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv] at h72
  have hVcp : ⁅Vc, Vc⁆ = Vc := by
    have h1 : ⁅V.subgroupOf Nb, V.subgroupOf Nb⁆ = V.subgroupOf Nb := by
      apply Subgroup.map_injective Nb.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hVL, hVp]
    rw [← Subgroup.map_commutator, h1]
  have hbot : Vc = ⊥ := by
    by_contra hne
    have : Nontrivial Vc := (Subgroup.nontrivial_iff_ne_bot Vc).mpr hne
    have : Group.IsPerfect Vc := Subgroup.isPerfect_iff.mpr hVcp
    exact Group.IsPerfect.not_isSolvable Vc (isSolvable_of_card_dvd_seventyTwo h72)
  have hu : c ⟨u, hVL huV⟩ ∈ Vc := ⟨_, Subgroup.mem_subgroupOf.mpr huV, rfl⟩
  rw [hbot, Subgroup.mem_bot, hkerc] at hu
  exact huC hu

end ToralReduce

end CFSG.AGLEmbedding
