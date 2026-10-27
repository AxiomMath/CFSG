module

public import CFSG.GH74.QTGen4.GL4.Embed
public import CFSG.GH74.QTGen4.GL4.Singer
public import CFSG.GH74.QTGen4.OrderOverH
public import CFSG.Quasithin.Vol2.Ch5StatementsB
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.GH74.QTGen4

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem exists_embedding_of_card_eq (hG : Gen4 G)
    (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {H K : Subgroup G}
    (hH : CFSG.Quasithin.InH (T : Subgroup G) H) (hKH : K ≤ H)
    (hK : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 20160) :
    ∃ ψ : ↥K ⧸ CFSG.pCore 2 ↥K →* GL (Fin 4) (ZMod 2), Function.Injective ψ := by
  have hchar := CFSG.Quasithin.charTwo_of_inH hEven T hH
  obtain ⟨ψH, hψH⟩ := exists_injective_quotient_pCore_to_GL4
    (isCharacteristicP_of_charTwo hchar) (Gen4.subgroup H hG)
  let f : ↥K →* ↥H ⧸ CFSG.pCore 2 ↥H := (QuotientGroup.mk' _).comp (Subgroup.inclusion hKH)
  let g : ↥K →* GL (Fin 4) (ZMod 2) := ψH.comp f
  have hgker : g.ker = f.ker := by
    ext x
    simp only [MonoidHom.mem_ker, g, MonoidHom.comp_apply]
    exact ⟨fun h => hψH (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  have hker : f.ker ≤ CFSG.pCore 2 ↥K := by
    have hn : f.ker.Normal := MonoidHom.normal_ker f
    have hp : IsPGroup 2 f.ker := by
      have h2 : IsPGroup 2 (CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup
      let g' : f.ker →* ↥(CFSG.pCore 2 ↥H) :=
        { toFun := fun k => ⟨Subgroup.inclusion hKH k.1, (QuotientGroup.eq_one_iff _).1 k.2⟩
          map_one' := rfl
          map_mul' := fun a b => rfl }
      refine IsPGroup.of_injective h2 g' (fun a b hab => ?_)
      have h1 : Subgroup.inclusion hKH a.1 = Subgroup.inclusion hKH b.1 :=
        congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => (z : ↥H)) hab
      have h2 : (a.1 : G) = b.1 := congrArg (fun z : ↥H => (z : G)) h1
      exact Subtype.ext (Subtype.ext h2)
    exact le_sSup ⟨hn, hp⟩
  let π : ↥K ⧸ g.ker →* ↥K ⧸ CFSG.pCore 2 ↥K :=
    QuotientGroup.map g.ker (CFSG.pCore 2 ↥K) (MonoidHom.id _) (hgker ▸ hker)
  have hπsurj : Function.Surjective π := fun x => by
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk k, rfl⟩
  have hle : Nat.card (↥K ⧸ g.ker) ∣ 20160 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
    exact (Subgroup.card_subgroup_dvd_card g.range).trans (by rw [card_GL4_two])
  have hge : 20160 ∣ Nat.card (↥K ⧸ g.ker) := hK ▸ Subgroup.card_dvd_of_surjective hπsurj
  have hcard : Nat.card (↥K ⧸ g.ker) = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [hK]; exact Nat.dvd_antisymm hle hge
  have hπinj : Function.Injective π := (hπsurj.bijective_of_nat_card_le hcard.le).1
  have hle2 : CFSG.pCore 2 ↥K ≤ g.ker := by
    intro x hx
    have h1 : π (QuotientGroup.mk x) = 1 := (QuotientGroup.eq_one_iff _).2 hx
    have h2 : (QuotientGroup.mk x : ↥K ⧸ g.ker) = 1 := hπinj (h1.trans (map_one π).symm)
    exact (QuotientGroup.eq_one_iff _).1 h2
  refine ⟨QuotientGroup.lift (CFSG.pCore 2 ↥K) g hle2,
    (injective_iff_map_eq_one _).2 fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : g x = 1 := hy
  have : x ∈ CFSG.pCore 2 ↥K := (hgker ▸ hker) hx
  exact (QuotientGroup.eq_one_iff _).2 this

theorem no_L34_modO2_of_inH (hG : Gen4 G)
    (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G)
    {H K : Subgroup G} (hH : CFSG.Quasithin.InH (T : Subgroup G) H) (hKH : K ≤ H)
    (hK : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 2) : False := by
  have hst := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hK
  have hq : CFSG.Quasithin.IsPSLEps3q true 4 (↥K ⧸ CFSG.pCore 2 ↥K) :=
    ⟨2, 2, Nat.prime_two, by norm_num, by norm_num, hst⟩
  obtain ⟨-, hcard⟩ := CFSG.Quasithin.H13.L34.card_of_isPSLEps3q hq
  have h20160 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 20160 := by
    rw [hcard]
    decide +kernel
  obtain ⟨ψ, hψ⟩ := exists_embedding_of_card_eq hG hEven T hH hKH h20160
  exact no_L34_into_GL4 ψ hψ hK

theorem stmt5_1_23_offender_gen4 :
    ∀ (G : Type) [Group G] [Finite G], Gen4 G →
      ∀ (T M L V H B D D₃ Z₁ : Subgroup G) (n : ℕ),
      Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
      LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
      D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
      ¬ IsMulCommutative ↥(conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))) →
        ∃ hU : IsElemAbelian 2 (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
            (Subgroup.centralizer (Z₁ : Set G)))),
          qhatInt (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
            (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))) hU <
            2 := by
  intro G _ _ hG T M L V H B D D₃ Z₁ n h _ _ hL34 _ _ _ _ _
  exfalso
  obtain ⟨P, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  exact no_L34_modO2_of_inH hG h.qtke.2.1 P h.hStar.1 (oTwoUpper_le H) hL34

end CFSG.GH74.QTGen4
