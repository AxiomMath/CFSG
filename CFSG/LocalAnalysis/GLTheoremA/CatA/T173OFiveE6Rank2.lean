module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveE6Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
open CFSG.StandardType.TableBExc.E6Three
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} {x : Ω} {F : Type} [Field F] [Finite F]


private theorem isElemAbelian_torusLift_sup_center_sup_zpowers
    [CharP F 2] (hq : 4 ≤ Nat.card F)
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3) (hx3 : x ^ 3 = 1)
    (hxcent : x ∈ Subgroup.centralizer (S : Set Ω))
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ζ : Fˣ} (hζ : orderOf ζ = 3)
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g) :
    IsElemAbelian 3
      (((Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
          Subgroup.center ↥S).map S.subtype) ⊔ Subgroup.zpowers x) := by
  refine isElemAbelian_sup_of_commute
    ((isElemAbelian_torusLift_sup_center hq hZ hζ hψ).map S.subtype)
    (CFSG.Open.isElemAbelian_zpowers hx3) ?_
  intro a ha b hb
  have haS : (a : Ω) ∈ S := Subgroup.map_subtype_le _ ha
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hb
  have hax : Commute a x := Subgroup.mem_centralizer_iff.1 hxcent a haS
  rw [← hn]
  exact hax.zpow_right n

private theorem not_mem_of_center_card_one
    (hZ1 : Nat.card (Subgroup.center ↥S) = 1)
    (hxcent : x ∈ Subgroup.centralizer (S : Set Ω)) (hx1 : x ≠ 1) : x ∉ S := by
  intro hxS
  have hxZ : (⟨x, hxS⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 hxcent (s : Ω) s.2
  have hbot : Subgroup.center ↥S = ⊥ := Subgroup.card_eq_one.1 hZ1
  rw [hbot, Subgroup.mem_bot] at hxZ
  exact hx1 (by simpa using congrArg Subtype.val hxZ)

private theorem three_pow_six_le_card_torusLift_of_center_trivial
    [CharP F 2]
    (hZ1 : Nat.card (Subgroup.center ↥S) = 1) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxcent : x ∈ Subgroup.centralizer (S : Set Ω))
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ζ : Fˣ} (hζ : orderOf ζ = 3)
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g) :
    3 ^ 6 ≤ Nat.card ↥(((Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
      Subgroup.center ↥S).map S.subtype) ⊔ Subgroup.zpowers x) := by
  classical
  have hAcard := card_torusLift_sup_center (M := M) (ζ := ζ) hζ hψ
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hAcard' : Nat.card ↥(Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
      Subgroup.center ↥S) = 3 ^ 5 := by rw [hAcard, hZ1, mul_one]
  have hxS : x ∉ S := not_mem_of_center_card_one hZ1 hxcent hx1
  have hKbot : Subgroup.zpowers x ⊓ S = ⊥ := by
    set K : Subgroup Ω := Subgroup.zpowers x ⊓ S with hK
    have hKdvd : Nat.card K ∣ 3 :=
      (Subgroup.card_dvd_of_le (H := K) (K := Subgroup.zpowers x) inf_le_left).trans
        (by rw [Nat.card_zpowers, hxord])
    rcases (Nat.dvd_prime Nat.prime_three).1 hKdvd with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have hEq : K = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hxord])
      exact hxS (by
        have hxK : x ∈ K := by rw [hEq]; exact Subgroup.mem_zpowers x
        exact (Subgroup.mem_inf.1 hxK).2)
  have hdisj : ((Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
      Subgroup.center ↥S).map S.subtype) ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzA, hzx⟩
    have hzK : z ∈ Subgroup.zpowers x ⊓ S :=
      Subgroup.mem_inf.2 ⟨hzx, Subgroup.map_subtype_le _ hzA⟩
    rw [hKbot] at hzK
    exact hzK
  have hcomm : ∀ a ∈ ((Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
      Subgroup.center ↥S).map S.subtype), ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    have haS : (a : Ω) ∈ S := Subgroup.map_subtype_le _ ha
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hax : Commute a x := Subgroup.mem_centralizer_iff.1 hxcent a haS
    rw [← hn]
    exact hax.zpow_right n
  have hcard_sup := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (((Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
      Subgroup.center ↥S).map S.subtype)) (Subgroup.zpowers x) hcomm).1
  rw [hdisj, Subgroup.card_bot, mul_one,
    Subgroup.card_map_of_injective S.subtype_injective, hAcard',
    Nat.card_zpowers, hxord] at hcard_sup
  rw [hcard_sup]
  norm_num

private theorem three_pow_six_le_card_torusLift
    [CharP F 2]
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxcent : x ∈ Subgroup.centralizer (S : Set Ω))
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ζ : Fˣ} (hζ : orderOf ζ = 3)
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g) :
    3 ^ 6 ≤ Nat.card ↥(((Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
      Subgroup.center ↥S).map S.subtype) ⊔ Subgroup.zpowers x) := by
  classical
  have hAcard := card_torusLift_sup_center (M := M) (ζ := ζ) hζ hψ
  rcases (Nat.dvd_prime Nat.prime_three).1 hZ with hZ1 | hZ3
  · exact three_pow_six_le_card_torusLift_of_center_trivial hZ1 hx3 hx1 hxcent hζ hψ
  · have hAcard3 : Nat.card ↥(Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
        Subgroup.center ↥S) = 3 ^ 6 := by rw [hAcard, hZ3]; norm_num
    calc 3 ^ 6 = Nat.card ↥(Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
          Subgroup.center ↥S) := hAcard3.symm
      _ = Nat.card ↥(((Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
            Subgroup.center ↥S).map S.subtype)) :=
          (Subgroup.card_map_of_injective S.subtype_injective).symm
      _ ≤ Nat.card ↥(((Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
            Subgroup.center ↥S).map S.subtype) ⊔ Subgroup.zpowers x) :=
          Subgroup.card_le_of_le le_sup_left

private theorem mem_normalizer_unipotent_of_torusLift
    [CharP F 2] (hZ : Nat.card (Subgroup.center ↥S) ∣ 3)
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ζ : Fˣ} (hζ : orderOf ζ = 3)
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g)
    (i : Fin Tag.E6.rank) :
    ((ψ i (HSL ζ) : ↥S) : Ω) ∈ Subgroup.normalizer
      (((unipotentSL2 F).map (ψ 0)).map S.subtype : Set Ω) := by
  set g : Ω := ((ψ i (HSL ζ) : ↥S) : Ω) with hg
  have hmap_le : (((unipotentSL2 F).map (ψ 0)).map S.subtype).map
      (MulAut.conj g).toMonoidHom ≤ ((unipotentSL2 F).map (ψ 0)).map S.subtype := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    simpa [MulAut.conj_apply, hg] using conj_mem_unipotent_of_torusLift hZ hψ i ζ hy'
  have hmap_eq : (((unipotentSL2 F).map (ψ 0)).map S.subtype).map
      (MulAut.conj g).toMonoidHom = ((unipotentSL2 F).map (ψ 0)).map S.subtype :=
    Subgroup.eq_of_le_of_card_ge hmap_le
      (by rw [Subgroup.card_map_of_injective (K := ((unipotentSL2 F).map (ψ 0)).map S.subtype)
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 hmap_eq

private theorem le_normalizer_unipotent_of_torusLift
    [CharP F 2] (hZ : Nat.card (Subgroup.center ↥S) ∣ 3)
    (hxcent : x ∈ Subgroup.centralizer (S : Set Ω))
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ζ : Fˣ} (hζ : orderOf ζ = 3)
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g) :
    (((Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
        Subgroup.center ↥S).map S.subtype) ⊔ Subgroup.zpowers x) ≤
      Subgroup.normalizer (((unipotentSL2 F).map (ψ 0)).map S.subtype : Set Ω) := by
  rw [Subgroup.map_sup]
  refine sup_le (sup_le ?_ ?_) (Subgroup.zpowers_le.2 ?_)
  · rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨z, ⟨i, rfl⟩, rfl⟩
    exact mem_normalizer_unipotent_of_torusLift hZ hζ hψ i
  · intro z hz
    obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.1 hz
    refine Subgroup.centralizer_le_normalizer _ ?_
    intro y hy
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.1 hy
    rw [← hcz, ← hsy]
    exact congrArg (fun w : ↥S => (w : Ω)) (Subgroup.mem_center_iff.1 hc s)
  · have hmap_le : (((unipotentSL2 F).map (ψ 0)).map S.subtype).map
        (MulAut.conj x).toMonoidHom ≤ ((unipotentSL2 F).map (ψ 0)).map S.subtype := by
      rintro z ⟨y, hy, rfl⟩
      have hyS : (y : Ω) ∈ S := Subgroup.map_subtype_le _ hy
      have hc : x * y = y * x := (Subgroup.mem_centralizer_iff.1 hxcent y hyS).symm
      change x * y * x⁻¹ ∈ Subgroup.map S.subtype (Subgroup.map (ψ 0) (unipotentSL2 F))
      rw [show x * y * x⁻¹ = y from by
        calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [hc]
          _ = y := by group]
      exact hy
    have hmap_eq : (((unipotentSL2 F).map (ψ 0)).map S.subtype).map
        (MulAut.conj x).toMonoidHom = ((unipotentSL2 F).map (ψ 0)).map S.subtype :=
      Subgroup.eq_of_le_of_card_ge hmap_le
        (by rw [Subgroup.card_map_of_injective (K := ((unipotentSL2 F).map (ψ 0)).map S.subtype)
        (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective])
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 hmap_eq

private theorem exists_twoGroup_normalized_by_torusLift
    [CharP F 2] (hZ : Nat.card (Subgroup.center ↥S) ∣ 3)
    (hxcent : x ∈ Subgroup.centralizer (S : Set Ω))
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ζ : Fˣ} (hζ : orderOf ζ = 3)
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g) :
    ∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      (((Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
          Subgroup.center ↥S).map S.subtype) ⊔ Subgroup.zpowers x) ≤
        Subgroup.normalizer (U : Set Ω) := by
  have hUne : ((unipotentSL2 F).map ((S.subtype).comp (ψ 0))) ≠ ⊥ :=
    unipotent_lift_ne_bot hψ
  have hU2 : IsPGroup 2 ↥((unipotentSL2 F).map ((S.subtype).comp (ψ 0))) :=
    isElemAbelian_unipotent.isPGroup.map ((S.subtype).comp (ψ 0))
  refine ⟨(unipotentSL2 F).map ((S.subtype).comp (ψ 0)), hUne, hU2, ?_⟩
  rw [show (unipotentSL2 F).map ((S.subtype).comp (ψ 0)) =
      ((unipotentSL2 F).map (ψ 0)).map S.subtype from by rw [Subgroup.map_map]]
  exact le_normalizer_unipotent_of_torusLift hZ hxcent hζ hψ

theorem three_pow_six_le_card_B {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} (hcfg : Cfg173 3 S B N D K x) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hq : 4 ≤ Nat.card F) (h3 : 3 ∣ Nat.card F - 1)
    (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3) : 3 ^ 6 ≤ Nat.card B := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fˣ, orderOf ζ = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : Fintype F := Fintype.ofFinite F
    have hdvd : 3 ∣ Fintype.card Fˣ := by
      rw [← Nat.card_eq_fintype_card, Nat.card_units F]
      exact h3
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card 3 hdvd
    exact ⟨ζ, hζ⟩
  choose ψ hψ using fun i : Fin Tag.E6.rank => exists_rootSL2_lift hq M hZ i
  have hx3 : x ^ 3 = 1 := hcfg.elem.2 x hcfg.mem
  have hx1 : x ≠ 1 := hcfg.ne_one
  have hxcent : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  let E : Subgroup Ω := ((Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
    Subgroup.center ↥S).map S.subtype) ⊔ Subgroup.zpowers x
  have hEel : IsElemAbelian 3 E :=
    isElemAbelian_torusLift_sup_center_sup_zpowers hq hZ hx3 hxcent hζ hψ
  have hEcard : 3 ^ 6 ≤ Nat.card ↥E :=
    three_pow_six_le_card_torusLift hZ hx3 hx1 hxcent (ζ := ζ) hζ hψ
  obtain ⟨U, hUne, hU2, hEN⟩ :=
    exists_twoGroup_normalized_by_torusLift hZ hxcent (ζ := ζ) hζ hψ
  have hle := card_le_pow_glaTwoLocalRank hcfg.prime hEel hUne hU2 hEN
  rw [← hcfg.bmax.2.1] at hle
  exact hEcard.trans hle

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
