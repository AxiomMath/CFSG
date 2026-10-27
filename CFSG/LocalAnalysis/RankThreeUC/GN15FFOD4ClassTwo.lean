module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Carrier
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Types
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Invol
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4ElemBound
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4SylowInner
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OuterTransvection

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
open CFSG.Quasithin
open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley

theorem exists_natural_of_quadratic_offender_card_two
    {K : Type} [Field K] [Finite K]
    [CharP K 2]
    (hK : Nat.card K = 2) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (L E : Subgroup (MulAut V)) (θ : L ≃* orthElementaryGroup (quadPlus 4 K))
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hE : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    (hEq : IsQuadratic E) (hoff : Nat.card V ≤ Nat.card E * Nat.card (fixV E)) :
    ∃ (ψ : L ≃* orthElementaryGroup (quadPlus 4 K)) (φ : Additive V ≃+ (Fin 4 ⊕ Fin 4 → K)),
      ∀ (l : L) (v : V), φ (Additive.ofMul ((l : MulAut V) v)) =
        (ψ l : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (φ (Additive.ofMul v)) :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module K (Additive V) := binModule hK hV
  letI : Module.Finite K (Additive V) := Module.Finite.of_finite
  PLift.down ⟨by
    classical
    have _hEq := hEq
    let ι : adjointGroup .D4 K →* MulAut V :=
      L.subtype.comp (θ.symm.toMonoidHom.comp (eta K).toMonoidHom)
    let ρ : Representation K (adjointGroup .D4 K) (Additive V) := binRep hK hV ι
    have hι : ∀ l ∈ L, ∃ g, ι g = l :=
      fun l hl => ⟨(eta K).symm (θ ⟨l, hl⟩), by simp [ι]⟩
    have hρ : IsSimpleRep ρ := by
      simpa [ρ] using isSimpleRep_binRep hK hV ι hirr hι
    have hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α :=
      ⟨_, invWord_four_smul⟩
    obtain ⟨y, χ, J, ht⟩ := exists_isChevType (p := 2) (hw := hw) (k := K) hρ
    by_cases hJu : J = Finset.univ
    ·
      have htA : IsChevType .D4 K 2 hw ρ y χ Finset.univ := hJu ▸ ht
      have htriv : ∀ (g : adjointGroup .D4 K) (w : Additive V), ρ g w = w :=
        eq_of_isChevType_univ hK hρ htA
      have hL1 : ∀ l : L, (l : MulAut V) = 1 := by
        intro l
        ext v
        have h2 : ρ ((eta K).symm (θ l)) (Additive.ofMul v) =
            Additive.ofMul ((l : MulAut V) v) := by
          rw [show ρ = binRep hK hV ι from rfl, binRep_apply]
          simp [ι]
        have h1 := htriv ((eta K).symm (θ l)) (Additive.ofMul v)
        rw [h2] at h1
        simpa using Additive.ofMul.injective h1
      have hne : θ.symm (eta K (xC .D4 K (0 : Fin 4) (1 : Kˣ))) ≠ 1 := by
        intro h
        have h1 : eta K (xC .D4 K (0 : Fin 4) (1 : Kˣ)) = 1 := by
          have := congrArg θ h
          simpa using this
        exact xC_ne_one (τ := .D4) (K := K) (0 : Fin 4) (1 : Kˣ)
          ((eta K).injective (by simpa using h1))
      exact absurd (Subtype.ext (hL1 (θ.symm (eta K (xC .D4 K (0 : Fin 4) (1 : Kˣ)))))) hne
    · by_cases hJe : ∃ e ∈ ({0, 1, 3} : Finset (Fin 4)), J = Finset.univ.erase e
      ·
        obtain ⟨e, he, hJ⟩ := hJe
        have htJ : IsChevType .D4 K 2 hw ρ y χ (Finset.univ.erase e) := hJ ▸ ht
        have ht1 : IsChevType .D4 K 2 hw ρ y (fun _ => 1) (Finset.univ.erase e) :=
          isChevType_one_of_card_two hK htJ
        obtain ⟨σ, β, hβ⟩ := exists_iso_natRep hK hρ he ht1
        let ψ : L ≃* orthElementaryGroup (quadPlus 4 K) :=
          θ.trans ((eta K).symm.trans (σ.trans (eta K)))
        refine ⟨ψ, β.toAddEquiv, ?_⟩
        intro l v
        let g : adjointGroup .D4 K := (eta K).symm (θ l)
        have hrep : ρ g (Additive.ofMul v) = Additive.ofMul ((l : MulAut V) v) := by
          rw [show ρ = binRep hK hV ι from rfl, binRep_apply]
          simp [g, ι]
        have h1 := hβ g (Additive.ofMul v)
        rw [hrep] at h1
        simpa [ψ, g, MulEquiv.trans_apply] using h1
      ·
        push Not at hJe
        have hrank : ∀ x ∈ L, x ≠ 1 → x * x = 1 →
            2 ^ 9 * Nat.card {v : V // x v = v} ≤ Nat.card V := by
          intro x hx hx1 hx2
          let g : adjointGroup .D4 K := (eta K).symm (θ ⟨x, hx⟩)
          have hxg : θ ⟨x, hx⟩ * θ ⟨x, hx⟩ = 1 := by
            have h : (⟨x, hx⟩ : L) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
            calc θ ⟨x, hx⟩ * θ ⟨x, hx⟩ = θ ((⟨x, hx⟩ : L) * ⟨x, hx⟩) := by rw [map_mul]
              _ = 1 := by rw [h, map_one]
          have hg2 : g * g = 1 := by
            rw [show g = (eta K).symm (θ ⟨x, hx⟩) from rfl, ← map_mul, hxg, map_one]
          have hg1 : g ≠ 1 := by
            intro h
            apply hx1
            have h' : θ ⟨x, hx⟩ = 1 := by
              have := congrArg (eta K) h
              simpa [g] using this
            have h1 : (⟨x, hx⟩ : L) = 1 := θ.injective (by rw [h', map_one])
            exact Subtype.ext_iff.mp h1
          have h9 : 9 ≤ Module.finrank K (LinearMap.range (binRep hK hV ι g - 1)) :=
            nine_le_finrank_range_of_sq_eq_one hρ ht hJu hJe g hg2 hg1
          have hcard := card_eq_card_fix_mul_two_pow hK hV ι g
          have hιg : ι g = x := by simp [g, ι]
          have hcard' : Nat.card V = Nat.card {v : V // x v = v} *
              2 ^ Module.finrank K (LinearMap.range (binRep hK hV ι g - 1)) := by
            rw [hcard, hιg]
          have hpow : 2 ^ 9 ≤ 2 ^ Module.finrank K
              (LinearMap.range (binRep hK hV ι g - 1)) :=
            Nat.pow_le_pow_right (by norm_num) h9
          calc 2 ^ 9 * Nat.card {v : V // x v = v}
              ≤ 2 ^ Module.finrank K (LinearMap.range (binRep hK hV ι g - 1)) *
                  Nat.card {v : V // x v = v} := Nat.mul_le_mul_right _ hpow
            _ = Nat.card V := by rw [hcard', Nat.mul_comm]
        by_cases hInt : E ⊓ L = ⊥
        ·
          have hE2 : Nat.card E ≤ 2 := by
            have h2 := card_le_two_mul_card_inf hK hV L E θ hirr hEN hEel
            rw [hInt, Subgroup.card_bot] at h2
            omega
          obtain ⟨v, hv⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
          have heE : (v : MulAut V) ∈ E := v.2
          have he1 : (v : MulAut V) ≠ 1 := fun h => hv (Subtype.ext h)
          have he2 : (v : MulAut V) * (v : MulAut V) = 1 := by
            simpa [pow_two] using hEel.2 (v : MulAut V) heE
          have heL : (v : MulAut V) ∉ L := by
            intro hL
            have hmem : (v : MulAut V) ∈ E ⊓ L := Subgroup.mem_inf.mpr ⟨heE, hL⟩
            rw [hInt] at hmem
            exact he1 (Subgroup.mem_bot.mp hmem)
          have hcardV : Nat.card V = 2 * Nat.card {w : V // (v : MulAut V) w = w} := by
            refine le_antisymm ?_ ?_
            · calc Nat.card V ≤ Nat.card E * Nat.card (fixV E) := hoff
                _ ≤ 2 * Nat.card {w : V // (v : MulAut V) w = w} := by
                    refine Nat.mul_le_mul hE2 ?_
                    refine Nat.card_le_card_of_injective
                      (fun u : fixV E => (⟨u.1, u.2 (v : MulAut V) heE⟩ :
                        {w : V // (v : MulAut V) w = w})) ?_
                    intro u w huw
                    exact Subtype.ext
                      (congrArg (fun z : {w : V // (v : MulAut V) w = w} => z.1) huw)
            · let S : Subgroup V :=
                { carrier := {w | (v : MulAut V) w = w}
                  one_mem' := map_one (v : MulAut V)
                  mul_mem' := by
                    intro a b ha hb
                    simp only [Set.mem_setOf_eq] at ha hb ⊢
                    rw [map_mul, ha, hb]
                  inv_mem' := by
                    intro a ha
                    simp only [Set.mem_setOf_eq] at ha ⊢
                    rw [map_inv, ha] }
              have hScard : Nat.card {w : V // (v : MulAut V) w = w} = Nat.card S :=
                Nat.card_congr
                  { toFun := fun x => ⟨x.1, show (v : MulAut V) x.1 = x.1 from x.2⟩
                    invFun := fun x => ⟨x.1, show (v : MulAut V) x.1 = x.1 from x.2⟩
                    left_inv := fun x => rfl
                    right_inv := fun x => rfl }
              have hSne : S ≠ ⊤ := by
                intro htop
                apply he1
                ext w
                have hw : w ∈ S := by rw [htop]; exact Subgroup.mem_top w
                exact hw
              have hidx1 : S.index ≠ 1 := fun h => hSne (Subgroup.index_eq_one.mp h)
              have hidx0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
              have hidx2 : 2 ≤ S.index := by omega
              have hcardmul := Subgroup.card_mul_index S
              calc 2 * Nat.card {w : V // (v : MulAut V) w = w}
                  = 2 * Nat.card S := by rw [hScard]
                _ ≤ S.index * Nat.card S := Nat.mul_le_mul_right _ hidx2
                _ = Nat.card S * S.index := Nat.mul_comm _ _
                _ = Nat.card V := hcardmul
          have hd : Nat.card V = 2 ^ Module.finrank K (Additive V) := by
            calc Nat.card V = Nat.card (Additive V) := (Nat.card_congr Additive.toMul).symm
              _ = Nat.card K ^ Module.finrank K (Additive V) := Module.natCard_eq_pow_finrank
              _ = 2 ^ Module.finrank K (Additive V) := by rw [hK]
          have hinv : ∀ x ∈ L, x ≠ 1 → x * x = 1 →
              2 ^ 5 * Nat.card {w : V // x w = w} ≤ Nat.card V := by
            intro x hx hx1 hx2
            exact le_trans (Nat.mul_le_mul_right _ (by norm_num : 2 ^ 5 ≤ 2 ^ 9))
              (hrank x hx hx1 hx2)
          have hodd : Odd ((Subgroup.centralizer {(v : MulAut V)}).subgroupOf L).index :=
            (CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.no_outer_transvection
              hV hirr (hEN heE) he2 hcardV hinv hd).1
          exact absurd (mem_of_odd_index_centralizer hV θ hirr (hEN heE) he2 hodd) heL
        ·
          obtain ⟨t, htne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hInt
          have htE : (t : MulAut V) ∈ E := (Subgroup.mem_inf.mp t.2).1
          have htL : (t : MulAut V) ∈ L := (Subgroup.mem_inf.mp t.2).2
          have ht1 : (t : MulAut V) ≠ 1 := fun h => htne (Subtype.ext h)
          have ht2 : (t : MulAut V) * (t : MulAut V) = 1 := by
            simpa [pow_two] using hEel.2 (t : MulAut V) htE
          have hcardInt : Nat.card (E ⊓ L : Subgroup (MulAut V)) ≤ 2 ^ 7 := by
            let A : Subgroup (orthElementaryGroup (quadPlus 4 K)) :=
              ((E ⊓ L).subgroupOf L).map θ.toMonoidHom
            have hcardA : Nat.card A = Nat.card (E ⊓ L : Subgroup (MulAut V)) := by
              rw [Subgroup.card_map_of_injective θ.injective]
              exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := E ⊓ L) (K := L)
                (inf_le_right)).toEquiv
            have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
              rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
              rw [← map_mul, ← map_mul]
              exact congrArg θ (Subtype.ext (hEel.1 (x : MulAut V)
                (Subgroup.mem_subgroupOf.mp hx).1 (y : MulAut V)
                (Subgroup.mem_subgroupOf.mp hy).1))
            have hsq : ∀ a ∈ A, a * a = 1 := by
              rintro _ ⟨x, hx, rfl⟩
              rw [← map_mul, ← map_one θ]
              exact congrArg θ (Subtype.ext (by
                simpa [pow_two] using hEel.2 (x : MulAut V)
                  (Subgroup.mem_subgroupOf.mp hx).1))
            have h7 := card_le_pow_seven_of_elemAbelian A hcomm hsq
            simpa [hcardA, hK] using h7
          have hcardE : Nat.card E ≤ 2 ^ 8 := by
            have h2 := card_le_two_mul_card_inf hK hV L E θ hirr hEN hEel
            calc Nat.card E ≤ 2 * Nat.card (E ⊓ L : Subgroup (MulAut V)) := h2
              _ ≤ 2 * 2 ^ 7 := by gcongr
              _ = 2 ^ 8 := by norm_num
          have hfixE : Nat.card (fixV E) ≤ Nat.card {v : V // (t : MulAut V) v = v} := by
            refine Nat.card_le_card_of_injective
              (fun u : fixV E => (⟨u.1, u.2 (t : MulAut V) htE⟩ :
                {v : V // (t : MulAut V) v = v})) ?_
            intro u w huw
            exact Subtype.ext (congrArg (fun z : {v : V // (t : MulAut V) v = v} => z.1) huw)
          have hVle : Nat.card V ≤ 2 ^ 8 * Nat.card {v : V // (t : MulAut V) v = v} :=
            calc Nat.card V ≤ Nat.card E * Nat.card (fixV E) := hoff
              _ ≤ 2 ^ 8 * Nat.card {v : V // (t : MulAut V) v = v} :=
                  Nat.mul_le_mul hcardE hfixE
          have hrt := hrank (t : MulAut V) htL ht1 ht2
          have hNe : Nonempty {v : V // (t : MulAut V) v = v} := ⟨⟨1, map_one (t : MulAut V)⟩⟩
          have hNpos : 0 < Nat.card {v : V // (t : MulAut V) v = v} := Nat.card_pos
          have hlt : 2 ^ 8 * Nat.card {v : V // (t : MulAut V) v = v} <
              2 ^ 9 * Nat.card {v : V // (t : MulAut V) v = v} :=
            Nat.mul_lt_mul_of_pos_right (by norm_num) hNpos
          exact absurd (le_trans hrt hVle) (not_le.mpr hlt)
  ⟩

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

end
