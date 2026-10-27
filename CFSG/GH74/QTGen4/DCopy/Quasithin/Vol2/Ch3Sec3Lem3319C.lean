module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3319A
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3319C

public section
namespace CFSG.Quasithin.H13.L3319

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open Matrix
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem false_of_sumNatDual_F4
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h12 : Step3_3_12R_F4) (hGA : CFSG.Open.GriessAllModelsStatement) (h51 : AsB51)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) [IsMulCommutative ↥(vPlus L T)]
    (e : ↥(autOn L (vPlus L T)) ≃* SpecialLinearGroup (Fin 5) (ZMod 2))
    (hB : B51Hyp (ffJ (autOn (L ⊔ T) (vPlus L T))) (autOn L (vPlus L T)))
    (hsnd : SumNatDual (autOn L (vPlus L T)) (commV (autOn L (vPlus L T))) 5) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := vPlus L T with hVdef
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hHV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.2.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hHV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hHV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hred.2.1.2 v v.2)
  have hcard : Nat.card ↥(autOn L V) = 9999360 := by
    rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 5 (Or.inr rfl)]
    rfl
  have hG := ffJ_eq_of_b51 hV2 h51 hB hcard
  have hS₀ : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal h.toSetup331.isSylowTwoOf le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  set T₀ := autOn (T ⊓ L) V with hT₀def
  have hT₀ : IsSylowTwoOf T₀ (autOn L V) := isSylowTwoOf_autOn hLV hS₀
  obtain ⟨-, -, -, -, -, hP6⟩ := h51 _ hV2 _ _ hB
  obtain ⟨⟨R, hRC, hR2, -, hRn, ⟨eR⟩⟩, hnoff⟩ := hP6 5 ⟨hG, hsnd⟩ T₀ (hG ▸ hT₀)
  set C := autOn L V ⊓ centSub (fixV T₀) with hCdef
  set Z₀ := V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) with hZ₀
  set H := L ⊓ Subgroup.centralizer (Z₀ : Set G) with hHdef
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hLV
  have hHC : autOn H V = C := autOn_inf_centralizer hLV inf_le_right
  obtain ⟨α, -, hαk, hαc⟩ := Ln2.exists_modO2Surj h hGA hTL (Nat.card_zmod 2) (by norm_num) le_rfl e
  have hCL2 : ∀ l : ↥L, (l : G) ∈ Subgroup.centralizer (V : Set G) → ∃ k : ℕ, l ^ 2 ^ k = 1 := by
    intro l hl
    have h1 : l ∈ α.ker := (hαc l).mpr hl
    rw [hαk] at h1
    exact CFSG.pCore_isPGroup ⟨l, h1⟩ |>.imp fun k hk => by
      have := congrArg Subtype.val hk
      simpa using this
  have hθ : ∀ x : ↥H, conjOf V H hHN x ∈ C := fun x => by
    rw [← hHC, ← range_conjOf hHN]
    exact ⟨x, rfl⟩
  let θ : ↥H →* ↥C := (conjOf V H hHN).codRestrict C hθ
  have hθs : Function.Surjective θ := by
    rintro ⟨c, hc⟩
    rw [← hHC, ← range_conjOf hHN] at hc
    obtain ⟨x, rfl⟩ := hc
    exact ⟨x, rfl⟩
  let f : ↥H →* SpecialLinearGroup (Fin 3) (ZMod 2) :=
    glEquivSL3.toMonoidHom.comp (eR.toMonoidHom.comp ((QuotientGroup.mk' (R.subgroupOf C)).comp θ))
  have hfs : Function.Surjective f :=
    glEquivSL3.surjective.comp (eR.surjective.comp ((QuotientGroup.mk'_surjective _).comp hθs))
  have hfker : f.ker = (R.subgroupOf C).comap θ := by
    rw [MonoidHom.ker_comp_of_injective _ _ glEquivSL3.injective,
      MonoidHom.ker_comp_of_injective _ _ eR.injective, ← MonoidHom.comap_ker,
      QuotientGroup.ker_mk']
  have hfk : IsPGroup 2 ↥f.ker := by
    rw [hfker]
    rintro ⟨x, hx⟩
    have hxR : ((θ x : ↥C) : MulAut ↥V) ∈ R := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨a, ha⟩ := hR2 ⟨_, hxR⟩
    have ha' : conjOf V H hHN (x ^ 2 ^ a) = 1 := by
      have h1 : ((θ x : ↥C) : MulAut ↥V) ^ 2 ^ a = 1 := by
        simpa using congrArg Subtype.val ha
      rw [map_pow]
      exact h1
    have hxC := (conjOf_eq_one_iff hHN _).mp ha'
    obtain ⟨b, hb⟩ := hCL2 ⟨((x ^ 2 ^ a : ↥H) : G), (x ^ 2 ^ a).2.1⟩ hxC
    refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_one, SubmonoidClass.coe_pow] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  obtain ⟨ψ, hψs, hψk⟩ := exists_hom_perfectCore commutator_sl3 f hfs hfk
  have hψk' : ψ.ker = CFSG.pCore 2 ↥(perfectCore H) :=
    Ln2.ker_eq_pCore_of_hom (Nat.card_zmod 2) le_rfl hψs hψk
  set Y := perfectCore H with hYdef
  have hYL : Y ≤ L := (perfectCore_le H).trans inf_le_left
  have hY : ⁅Y, Y⁆ = Y := perfectCore_perfect H
  have hTH : T ≤ Subgroup.normalizer (H : Set G) := by
    intro t ht
    have hTTL : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer ht) (hTL ht)
    exact ChiefCount.mem_normalizer_inf (hTL ht)
      (normalizer_le_normalizer_centralizer _ (ChiefCount.mem_normalizer_inf (hTV ht)
        (normalizer_le_normalizer_centralizer _ hTTL)))
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) :=
    hTH.trans (normalizer_le_normalizer_perfectCore H)
  have hZZ₀ : quasithinOmegaOneCenter T ≤ Z₀ := by
    refine le_inf (le_conjClosure _ _) ?_
    exact (B2F.omegaOneCenter_le_inf_centralizer T).trans
      (inf_le_right.trans (Subgroup.centralizer_le inf_le_left))
  have hYZ : Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    (perfectCore_le H).trans (inf_le_right.trans (Subgroup.centralizer_le hZZ₀))
  refine false_of_offender_F4 h h38 h39 h12 hYL hY hTY hYZ hψs hψk' fun B hB hBK => ?_
  have hBJ : B ≤ ffJ (autOn (L ⊔ T) V) := B19.le_ffJ hB
  have hBL : B ≤ autOn L V := hG ▸ hBJ
  apply hnoff B ⟨hBJ, hB.2⟩
  rw [hG]
  set P := pCoreOf 2 (Y ⊔ T) with hPdef
  set K := autOn P V with hKdef
  have hsylYT : IsSylowTwoOf T (Y ⊔ T) := ⟨le_sup_right, h.sylow.1, fun h2 =>
    h.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hPT : P ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylYT
  have hK2 : IsPGroup 2 ↥K :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Y ⊔ T)).comap_of_injective _
      (Subgroup.normalizer (V : Set G)).subtype_injective).map _
  have hT2 : IsPGroup 2 ↥(autOn T V) :=
    (h.sylow.1.comap_of_injective _ (Subgroup.normalizer (V : Set G)).subtype_injective).map _
  have heq : autOn T V ⊓ autOn L V = T₀ :=
    hT₀.eq_of_le (le_inf (autOn_le_autOn V inf_le_left) (autOn_le_autOn V inf_le_right))
      inf_le_right (hT2.to_le inf_le_left)
  have hQT₀ : K ⊓ autOn L V ≤ T₀ :=
    (inf_le_inf_right _ (autOn_le_autOn V hPT)).trans heq.le
  have hT₀C : T₀ ≤ C := le_inf hT₀.1 fun t ht v hv => hv t ht
  have hCL : C ≤ autOn L V := inf_le_left
  have hsylC : IsSylowTwoOf T₀ C := ⟨hT₀C, hT₀.2.1, fun h2 => hT₀.2.2 (by
    have h3 : 2 ∣ T₀.relIndex C := h2
    show 2 ∣ T₀.relIndex (autOn L V)
    rw [← Subgroup.relIndex_mul_relIndex T₀ C (autOn L V) hT₀C hCL]
    exact Dvd.dvd.mul_right h3 _)⟩
  have hRT₀ : R ≤ T₀ := hsylC.le_of_normalizes hRC
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp hRn) hR2
  have hperf : commutator (↥C ⧸ R.subgroupOf C) = ⊤ :=
    commutator_eq_top_of_equiv (eR.trans glEquivSL3) commutator_sl3
  have hCYT : C ≤ autOn (Y ⊔ T) V := by
    refine (le_perfectCore_sup hRn hperf).trans (sup_le ?_ ?_)
    · rw [← hHC, ← autOn_perfectCore hHN]
      exact autOn_le_autOn V le_sup_left
    · exact hRT₀.trans ((autOn_le_autOn V inf_le_left).trans (autOn_le_autOn V le_sup_right))
  have hCN : C ≤ Subgroup.normalizer ((K ⊓ autOn L V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) :=
    fun c hc => ChiefCount.mem_normalizer_inf
      (autOn_le_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ T)) (hCYT hc))
      (Subgroup.le_normalizer (hCL hc))
  exact (le_inf hBK hBL).trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hQT₀.trans hT₀C) hCN (hK2.to_le inf_le_left))

end CFSG.Quasithin.H13.L3319
