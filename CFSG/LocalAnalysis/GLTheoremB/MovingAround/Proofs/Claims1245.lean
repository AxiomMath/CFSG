module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1245
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1211
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129b
public import CFSG.LocalAnalysis.GL83PartI.I_22_5

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1245

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

@[expose] def Input31_10L34 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (X L : Subgroup G), GLAPComponent 3 X L →
    IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) →
    ∀ R : Subgroup G, IsSylowIn 3 X R → ∀ U V : Subgroup G, IsEkIn 3 4 R U → IsEkIn 3 4 R V →
      IsKConnectedIn 3 3 X U V

@[expose] def InputSL34SylowCent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    IsLThreeFour (Y ⧸ Subgroup.center Y) → Subgroup.center Y ≠ ⊥ →
    ∀ φ : MulAut Y, φ ^ 3 = 1 → ∀ P : Sylow 3 Y, (∀ y ∈ (P : Subgroup Y), φ y = y) → φ = 1

section Generic

variable {G : Type} [Group G] [Finite G]

theorem isEkIn_top_gLBConj' {p k : ℕ} {U : Subgroup G} (hU : IsEkIn p k ⊤ U) (g : G) :
    IsEkIn p k ⊤ (GLBConj g U) :=
  ⟨le_top, Lemma1112b.isElemAbelian_glbConj hU.2.1 g, (Lemma1112b.card_glbConj g U).trans hU.2.2⟩

theorem le_centralizer_gLBConj {U V : Subgroup G} (h : U ≤ Subgroup.centralizer (V : Set G)) (g : G) :
    GLBConj g U ≤ Subgroup.centralizer ((GLBConj g V : Subgroup G) : Set G) := by
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rw [mem_gLBConj] at hu
  have hv' : g * v * g⁻¹ ∈ V := mem_gLBConj.1 hv
  have hc := Subgroup.mem_centralizer_iff.1 (h hu) _ hv'
  have e : v * u = g⁻¹ * ((g * v * g⁻¹) * (g * u * g⁻¹)) * g := by group
  have e' : u * v = g⁻¹ * ((g * u * g⁻¹) * (g * v * g⁻¹)) * g := by group
  rw [e, e', hc]

theorem isKConnectedIn_top_gLBConj {p k : ℕ} {U V : Subgroup G} (h : IsKConnectedIn p k ⊤ U V)
    (g : G) : IsKConnectedIn p k ⊤ (GLBConj g U) (GLBConj g V) := by
  obtain ⟨-, hUel, hUc, -, hVel, hVc, hcase⟩ := h
  refine ⟨le_top, Lemma1112b.isElemAbelian_glbConj hUel g, by rw [Lemma1112b.card_glbConj]; exact hUc,
    le_top, Lemma1112b.isElemAbelian_glbConj hVel g, by rw [Lemma1112b.card_glbConj]; exact hVc, ?_⟩
  rcases hcase with hUV | ⟨U₁, V₁, hU₁, hV₁, hUU₁, hrt, hV₁V⟩
  · exact Or.inl (le_centralizer_gLBConj hUV g)
  · refine Or.inr ⟨GLBConj g U₁, GLBConj g V₁, isEkIn_top_gLBConj' hU₁ g, isEkIn_top_gLBConj' hV₁ g,
      le_centralizer_gLBConj hUU₁ g, ?_, le_centralizer_gLBConj hV₁V g⟩
    exact Relation.ReflTransGen.lift (GLBConj g) (fun W Y hWY =>
      ⟨isEkIn_top_gLBConj' hWY.1 g, isEkIn_top_gLBConj' hWY.2.1 g, le_centralizer_gLBConj hWY.2.2 g⟩)
      U₁ V₁ hrt

theorem isKConnectedIn_top_of {p k : ℕ} {X U V : Subgroup G} (h : IsKConnectedIn p k X U V) :
    IsKConnectedIn p k ⊤ U V := by
  obtain ⟨-, hUel, hUc, -, hVel, hVc, hcase⟩ := h
  refine ⟨le_top, hUel, hUc, le_top, hVel, hVc, ?_⟩
  rcases hcase with hc | ⟨U₁, V₁, hU₁, hV₁, hUU₁, hrt, hV₁V⟩
  · exact Or.inl hc
  · refine Or.inr ⟨U₁, V₁, ⟨le_top, hU₁.2.1, hU₁.2.2⟩, ⟨le_top, hV₁.2.1, hV₁.2.2⟩, hUU₁, ?_, hV₁V⟩
    have hstep : ∀ W Y : Subgroup G, IsKConnStep p k X W Y → IsKConnStep p k ⊤ W Y :=
      fun W Y hWY => ⟨⟨le_top, hWY.1.2.1, hWY.1.2.2⟩, ⟨le_top, hWY.2.1.2.1, hWY.2.1.2.2⟩, hWY.2.2⟩
    exact Relation.ReflTransGen.mono hstep _ _ hrt

theorem isSylowIn_top_subgroupOf' {Y P : Subgroup G} (hP : IsSylowIn 3 Y P) :
    IsSylowIn 3 (⊤ : Subgroup ↥Y) (P.subgroupOf Y) := by
  refine ⟨le_top, hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm, ?_⟩
  intro R' _ hR'3 hPR'
  have hmap : R'.map Y.subtype = P := by
    refine hP.2.2 (R'.map Y.subtype) ?_ (hR'3.map Y.subtype) ?_
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · intro q hq
      exact ⟨⟨q, hP.1 hq⟩, hPR' (by simpa [Subgroup.mem_subgroupOf] using hq), rfl⟩
  rw [← hmap]
  exact (Subgroup.comap_map_eq_self_of_injective Y.subtype_injective R').symm

theorem exists_conj_le_of_isSylowIn' {Y P R : Subgroup G} (hP : IsSylowIn 3 Y P) (hRY : R ≤ Y)
    (hR : IsPGroup 3 R) : ∃ y ∈ Y, ∀ r ∈ R, y⁻¹ * r * y ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP' := isSylowIn_top_subgroupOf' hP
  obtain ⟨g, hg⟩ := Lemma1112b.exists_glbConj_le_of_isSylowIn hP'
    (hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm : IsPGroup 3 (R.subgroupOf Y))
  refine ⟨(g : G), g.2, fun r hr => ?_⟩
  have hmem : (⟨r, hRY hr⟩ : ↥Y) ∈ R.subgroupOf Y := by simpa [Subgroup.mem_subgroupOf] using hr
  have h1 : (g⁻¹ * ⟨r, hRY hr⟩ * g : ↥Y) ∈ GLBConj g (R.subgroupOf Y) :=
    Lemma1112b.mem_glbConj.2 ⟨_, hmem, rfl⟩
  have h2 := hg h1
  simpa [Subgroup.mem_subgroupOf] using h2

theorem isSylowIn_inf_of_normal' {Y N P : Subgroup G} (hP : IsSylowIn 3 Y P) (hNY : N ≤ Y)
    (hn : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) : IsSylowIn 3 N (P ⊓ N) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨inf_le_right, hP.2.1.to_le inf_le_left, ?_⟩
  intro T hTN hT3 hPT
  obtain ⟨Q, hQ, hTQ⟩ := Lemma1112b.exists_isSylowIn_ge hTN hT3
  obtain ⟨y, hyY, hy⟩ := exists_conj_le_of_isSylowIn' hP (hQ.1.trans hNY) hQ.2.1
  have hcard : Nat.card Q ≤ Nat.card ↥(P ⊓ N) := by
    refine Nat.card_le_card_of_injective
      (fun q : Q => (⟨y⁻¹ * (q : G) * y, Subgroup.mem_inf.2 ⟨hy q q.2, ?_⟩⟩ : ↥(P ⊓ N))) ?_
    · have := hn y⁻¹ (Y.inv_mem hyY) q (hQ.1 q.2)
      simpa using this
    · intro q q' h
      apply Subtype.ext
      have h1 := congrArg Subtype.val h
      simp only [mul_left_inj, mul_right_inj] at h1
      exact h1
  have hTcard : Nat.card T ≤ Nat.card ↥(P ⊓ N) :=
    le_trans (Subgroup.card_le_of_le hTQ) hcard
  exact (Subgroup.eq_of_le_of_card_ge hPT hTcard).symm

theorem exists_sylow_of_isSylowIn {K T : Subgroup G} (hT : IsSylowIn 3 K T) :
    ∃ P : Sylow 3 ↥K, (P : Subgroup ↥K) = T.subgroupOf K := by
  refine ⟨⟨T.subgroupOf K, hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm, ?_⟩, rfl⟩
  intro Q hQ hTQ
  have hmap : Q.map K.subtype = T := by
    refine hT.2.2 (Q.map K.subtype) (Subgroup.map_subtype_le Q) (hQ.map K.subtype) ?_
    intro t ht
    exact ⟨⟨t, hT.1 ht⟩, hTQ (by simpa [Subgroup.mem_subgroupOf] using ht), rfl⟩
  rw [← hmap]
  exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q).symm

theorem exists_mem_centerOf_order_three {P : Subgroup G} (hP : IsPGroup 3 ↥P) (hne : P ≠ ⊥) :
    ∃ x : G, x ∈ centerOf P ∧ orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hne
  haveI : Nontrivial ↥(Subgroup.center ↥P) := hP.center_nontrivial
  obtain ⟨n, hn, hcard⟩ := (hP.to_subgroup (Subgroup.center ↥P)).nontrivial_iff_card.1 inferInstance
  have hdvd : 3 ∣ Nat.card ↥(Subgroup.center ↥P) := by
    rw [hcard]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨((z : ↥P) : G), Subgroup.mem_map.2 ⟨z, z.2, rfl⟩, ?_⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]

theorem comm_of_mem_centerOf {P : Subgroup G} {x : G} (hx : x ∈ centerOf P) :
    ∀ q ∈ P, q * x = x * q := by
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx
  intro q hq
  have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨q, hq⟩)
  rw [← hzx]
  exact h1

end Generic

section SylowEnd

variable {G : Type} [Group G] [Finite G]

theorem false_of_sylow_connected (h104i : Lemma104_iStatement) (h104ii : Lemma104_iiStatement)
    (h104iii : Lemma104_iiiStatement) (h104iv : Lemma104_ivStatement) (h104vi : Lemma104_viStatement)
    {m : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m 3 B M E A a)
    (hk : CFSG.Open.pRank 3 (E ⊓ A) = 2) (hA4 : CFSG.Open.pRank 3 A = 4)
    {P : Subgroup G} (hP : IsSylowIn 3 ⊤ P)
    (hconnP : ∀ U V : Subgroup G, IsEkIn 3 4 P U → IsEkIn 3 4 P V → IsKConnectedIn 3 3 ⊤ U V) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hSC : IsSCp 3 ⊤ A := (h104ii h.toSec11.toSec10Fails h.pair).2
  have hcardA : Nat.card A = 3 ^ 4 := Lemma124.card_eq_of_pRank_four hAel hA4
  have hEel : IsElemAbelian 3 E := h.pair.1.1.1.1.2.1
  have hEM : E ≤ M := h.pair.1.1.1.1.1
  have hE4 : 4 ≤ CFSG.Open.pRank 3 E := by
    have h3 : 3 ≤ CFSG.Open.pRank 3 E := h.pair.1.1.1.2
    by_contra hlt
    have hE3 : CFSG.Open.pRank 3 E = 3 := by omega
    have := h104vi h.toSec11.toSec10Fails h.pair hE3
    omega
  have hcardE : Nat.card E = 3 ^ CFSG.Open.pRank 3 E := Lemma124.card_eq_pow_pRank hEel
  obtain ⟨H4, hH4⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 3 (n := 4)
    (by rw [hcardE]; exact pow_dvd_pow 3 hE4)
  set E4 : Subgroup G := H4.map E.subtype with hE4def
  have hE4E : E4 ≤ E := Subgroup.map_subtype_le _
  have hE4card : Nat.card E4 = 3 ^ 4 := by
    rw [hE4def, Subgroup.card_map_of_injective E.subtype_injective, hH4]
  have hE4el : IsElemAbelian 3 E4 := Lemma124.isElemAbelian_of_le hE4E hEel
  have hEA3 : IsPGroup 3 ↥(E ⊔ A) := h104i h.toSec11.toSec10Fails h.pair
  obtain ⟨R, hR, hEAR⟩ := Lemma124.exists_isSylowIn_above_aux (sup_le hEM hAM) hEA3
  obtain ⟨-, -, hRG⟩ := h104iv h.toSec11.toSec10Fails h.pair hk hR
  have hAR : A ≤ R := le_sup_right.trans hEAR
  have hER : E ≤ R := le_sup_left.trans hEAR
  obtain ⟨g, hg⟩ := Lemma1112b.exists_glbConj_le_of_isSylowIn hRG hP.2.1
  have hgP : GLBConj g P = R :=
    ((Lemma1211.isSylowIn_top_gLBConj hP g).2.2 R le_top hRG.2.1 hg).symm
  have hRP : GLBConj g⁻¹ R = P := by rw [← hgP, gLBConj_inv_gLBConj]
  have hEk : ∀ U, IsEkIn 3 4 R U → IsEkIn 3 4 P (GLBConj g⁻¹ U) := fun U hU =>
    ⟨hRP ▸ gLBConj_mono g⁻¹ hU.1, Lemma1112b.isElemAbelian_glbConj hU.2.1 _,
      (Lemma1112b.card_glbConj _ _).trans hU.2.2⟩
  have hAk : IsEkIn 3 4 R A := ⟨hAR, hAel, hcardA⟩
  have hE4k : IsEkIn 3 4 R E4 := ⟨hE4E.trans hER, hE4el, hE4card⟩
  have hc2 := isKConnectedIn_top_gLBConj (hconnP _ _ (hEk A hAk) (hEk E4 hE4k)) g
  rw [gLBConj_gLBConj_inv, gLBConj_gLBConj_inv] at hc2
  have hc3 : IsKConnectedIn 3 3 ⊤ A E := Lemma116.isKConnectedIn_extend hp3 le_rfl hc2 le_rfl hE4E
    hAel hEel (by rw [hcardA]; norm_num)
    (by rw [hcardE]; exact Nat.pow_le_pow_right (by norm_num) (by omega)) le_top le_top
  have hconn : IsKConnectedIn 3 (CFSG.Open.pRank 3 (E ⊓ A) + 1) ⊤ A E := by
    rw [hk]
    exact hc3
  have hDA : inD 3 M A := h104iii h.toSec11.toSec10Fails h.pair hSC h.pair.1.1 hconn
  exact h.pair.1.2.1.2 hDA.2

end SylowEnd

section TypeClaim

theorem typeClaim_of_inputs (h122 : Lemma122_i_iiStatement) (h123 : Lemma123Statement)
    (h117 : Prop117_cex_falseStatement) (h104i : Lemma104_iStatement) (h104ii : Lemma104_iiStatement)
    (h104iii : Lemma104_iiiStatement) (h104iv : Lemma104_ivStatement) (h104vi : Lemma104_viStatement)
    (h3110 : Input31_10L34) (hSL : InputSL34SylowCent) :
    Lemma1245.TypeClaim := by
  intro G _ _ m B M E A a h K hK hK3 hKM hA0 hAN hKxcl
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  by_contra hZ
  have hA4 : CFSG.Open.pRank 3 A = 4 :=
    Lemma1245.pRank_eq_four_of_inputs h122 h123 h117 h104ii h104iii h104iv h hK hK3 hKM
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hSC : IsSCp 3 ⊤ A := (h104ii h.toSec11.toSec10Fails h.pair).2
  have hcardA : Nat.card A = 3 ^ 4 := Lemma124.card_eq_of_pRank_four hAel hA4
  have hYN : A ⊔ K ≤ Subgroup.normalizer (K : Set G) := sup_le hAN Subgroup.le_normalizer
  have hA3 : IsPGroup 3 ↥A := Lemma124.isPGroup_three_of_isElemAbelian hAel
  obtain ⟨S, hS, hAS⟩ := Lemma1112b.exists_isSylowIn_ge (le_sup_left : A ≤ A ⊔ K) hA3
  have hT : IsSylowIn 3 K (S ⊓ K) := isSylowIn_inf_of_normal' hS le_sup_right
    (fun y hy k hk => (Subgroup.mem_normalizer_iff.1 (hYN hy) k).1 hk)
  obtain ⟨P, hP, hSP⟩ := Lemma1112b.exists_isSylowIn_ge (le_top : S ≤ ⊤) hS.2.1
  have hAne : A ≠ ⊥ := by
    intro hbot
    rw [hbot] at hcardA
    simp at hcardA
  obtain ⟨x, hxZ, hxo⟩ := exists_mem_centerOf_order_three hP.2.1
    (ne_bot_of_le_ne_bot hAne (hAS.trans hSP))
  have hxA : x ∈ A := by
    have hU3 : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxo]
    have hUle : Subgroup.zpowers x ≤ centerOf P := (Subgroup.zpowers_le).2 hxZ
    exact Lemma1112b.le_of_centerOf_of_isSCp hAel hSC (hAS.trans hSP) hUle hU3
      (Subgroup.mem_zpowers x)
  have hx1 : x ≠ 1 := by
    intro hx
    rw [hx, orderOf_one] at hxo
    norm_num at hxo
  have hxcomm : ∀ q ∈ P, q * x = x * q := comm_of_mem_centerOf hxZ
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hAN hxA
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K) := l119_isQuasisimple_barOf (p := 3) (by norm_num) hK
  have hO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot (p := 3) (by norm_num)
  obtain ⟨T₀, hT₀⟩ := exists_sylow_of_isSylowIn hT
  set Pbar : Sylow 3 (barOf 3 K) :=
    T₀.mapSurjective (QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K)) with hPbar
  have hfix : ∀ y ∈ (Pbar : Subgroup (barOf 3 K)), barAut 3 K ⟨x, hxN⟩ y = y := by
    intro y hy
    rw [hPbar, Sylow.coe_mapSurjective, hT₀] at hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hy
    rw [QuotientGroup.mk'_apply, CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have htP : (t : G) ∈ P := hSP (Subgroup.mem_subgroupOf.1 ht).1
    have hc := hxcomm t htP
    calc x * (t : G) * x⁻¹ = ((t : G) * x) * x⁻¹ := by rw [hc]
      _ = t := by group
  have hpow : barAut 3 K ⟨x, hxN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have hx3 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hAel.2 x hxA)
    rw [hx3, map_one]
  have hbar1 : barAut 3 K ⟨x, hxN⟩ = 1 := hSL (barOf 3 K) hq hO hK3 hZ _ hpow Pbar hfix
  have hxF : x ∈ Lemma1245.FF A K :=
    ⟨Subgroup.mem_map.2 ⟨⟨x, hxN⟩, MonoidHom.mem_ker.2 hbar1, rfl⟩, hxA⟩
  obtain ⟨hKxc, hcovx⟩ := hKxcl x hxF hx1
  have hcovK : barX 3 K (Lemma1245.JJ A K) = ⊤ := Lemma1245.barX_JJ_eq_top hAel hq
  have hJK : Lemma1245.JJ A K ≤ K := (Sec12b.layer_le 3 _).trans inf_le_left
  obtain ⟨eK, -⟩ := Lemma1245.exists_barOf_equiv_of_cover (p := 3) hp3 hJK hcovK
  obtain ⟨eX, -⟩ := Lemma1245.exists_barOf_equiv_of_cover (p := 3) hp3
    (Sec12b.le_kx (p := 3) x (Lemma1245.JJ A K)) hcovx
  have hKxt : IsLThreeFour (barOf 3 (Kx 3 (Lemma1245.JJ A K) x) ⧸
      Subgroup.center (barOf 3 (Kx 3 (Lemma1245.JJ A K) x))) :=
    Lemma1245.isLThreeFour_modCenter_congr (eK.symm.trans eX) hK3
  have hPC : P ≤ Cg x := fun q hq => Subgroup.mem_centralizer_iff.2 (fun y hy => by
    rw [Set.mem_singleton_iff.1 hy]
    exact (hxcomm q hq).symm)
  have hPx : IsSylowIn 3 (Cg x) P := ⟨hPC, hP.2.1, fun R' _ hR' hPR' => hP.2.2 R' le_top hR' hPR'⟩
  have hconnP := h3110 (Cg x) _ hKxc hKxt P hPx
  exact false_of_sylow_connected h104i h104ii h104iii h104iv h104vi h
    (Lemma124.pRank_inter_eq_two_of_inputs h123 h) hA4 hP
    (fun U V hU hV => isKConnectedIn_top_of (hconnP U V hU hV))

end TypeClaim

@[expose] def InputL34Fix3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsLThreeFour Y → ∀ φ : MulAut Y, φ ^ 3 = 1 →
    ∀ Z : Subgroup Y, Nat.card Z ≤ 3 → ∃ w : Y, orderOf w = 3 ∧ φ w = w ∧ w ∉ Z

section UniqHelpers

variable {G : Type} [Group G] [Finite G]

theorem commute_of_glaPComponent_ne {X I L : Subgroup G} (hI : GLAPComponent 3 X I)
    (hL : GLAPComponent 3 X L) (hne : I ≠ L) {u v : ↥X ⧸ GLAPPrimeCore 3 ↥X}
    (hu : u ∈ barX 3 X I) (hv : v ∈ barX 3 X L) : u * v = v * u := by
  have hIc : CFSG.IsComponent (barX 3 X I) := (CFSG.isComponent_iff_open _).2 hI.2.2.1
  have hLc : CFSG.IsComponent (barX 3 X L) := (CFSG.isComponent_iff_open _).2 hL.2.2.1
  rcases CFSG.LocalCores.distinct_components_commute hIc hLc with heq | hcomm
  · exact absurd (glaPComponent_unique hI hL heq) hne
  · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact (Subgroup.mem_centralizer_iff.1 (hle hu) v hv).symm

theorem mem_barX_gLBConj {X I : Subgroup G} (hIX : I ≤ X) {y : G} (hy : y ∈ X)
    (z : ↥X ⧸ GLAPPrimeCore 3 ↥X) :
    z ∈ barX 3 X (GLBConj y I) ↔
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨y, hy⟩ * z *
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨y, hy⟩)⁻¹ ∈ barX 3 X I := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ z
  constructor
  · rintro ⟨d, hd, hdc⟩
    have hd' : (d : G) ∈ GLBConj y I := hd
    refine ⟨⟨y, hy⟩ * d * ⟨y, hy⟩⁻¹, ?_, ?_⟩
    · show y * (d : G) * y⁻¹ ∈ I
      exact mem_gLBConj.1 hd'
    · rw [map_mul, map_mul, map_inv, hdc]
  · rintro ⟨d, hd, hdc⟩
    have hd' : (d : G) ∈ I := hd
    refine ⟨⟨y, hy⟩⁻¹ * d * ⟨y, hy⟩, ?_, ?_⟩
    · show y⁻¹ * (d : G) * y ∈ GLBConj y I
      rw [mem_gLBConj]
      simpa [mul_assoc] using hd'
    · rw [map_mul, map_mul, map_inv, hdc]
      group

theorem center_barX_eq_bot {X I : Subgroup G} (hI : GLAPComponent 3 X I)
    (hc : Subgroup.center (barOf 3 I) = ⊥) : Subgroup.center ↥(barX 3 X I) = ⊥ :=
  Lemma1245.center_eq_bot_of_equiv
    (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barXEquiv Nat.prime_three hI.2.1).symm hc

theorem false_of_commute_of_isSCp {X A : Subgroup G} (hAX : A ≤ X) (hAel : IsElemAbelian 3 A)
    (hSC : IsSCp 3 ⊤ A) {w : ↥X ⧸ GLAPPrimeCore 3 ↥X} (hw3 : w ^ 3 = 1)
    (hwA : w ∉ barX 3 X A) (hcomm : ∀ z ∈ barX 3 X A, z * w = w * z) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set W : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) := Subgroup.zpowers w with hW
  have hWp : IsPGroup 3 ↥W := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hw3, one_zpow, Subgroup.coe_one]
  set H : Subgroup G := (W.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X))).map X.subtype with hH
  have hHX : H ≤ X := Subgroup.map_subtype_le _
  have hbarH : barX 3 X H = W := by
    apply le_antisymm
    · rintro z ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hc)
      have hdc' : d = c := Subtype.ext hdc
      rw [← hdc']
      exact Subgroup.mem_comap.1 hd
    · intro u hu
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥X) u
      exact ⟨c, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨c, Subgroup.mem_comap.2 hu, rfl⟩), rfl⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 ↥H) := inferInstance
  set V : Subgroup G := (Q : Subgroup ↥H).map H.subtype with hV
  have hVH : V ≤ H := Subgroup.map_subtype_le _
  have hV3 : IsPGroup 3 ↥V := Q.isPGroup'.map H.subtype
  have hbarV : barX 3 X V = W := (barX_sylow_eq hHX (by rw [hbarH]; exact hWp) Q).trans hbarH
  have hA3 : IsPGroup 3 ↥A := Lemma124.isPGroup_three_of_isElemAbelian hAel
  have hcommbar : barX 3 X A ≤ Subgroup.centralizer
      ((barX 3 X V : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    rw [hbarV]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    exact ((Commute.zpow_left (hcomm z hz).symm k).eq)
  obtain ⟨o, ho, hoc⟩ := exists_conj_commute hAX (hVH.trans hHX) hA3 hV3 hcommbar
  have hwV : w ∈ barX 3 X V := by rw [hbarV]; exact Subgroup.mem_zpowers w
  obtain ⟨v₀, hv₀, hv₀w⟩ := Subgroup.mem_map.1 hwV
  have hv₀V : (v₀ : G) ∈ V := Subgroup.mem_subgroupOf.1 hv₀
  have hoX : o ∈ X := sec11_glaPPrimeCoreOf_le X ho
  set v : G := o⁻¹ * (v₀ : G) * o with hvdef
  have hvX : v ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hoX) v₀.2) hoX
  have hvconj : v ∈ GLBConj o V := by
    rw [mem_gLBConj]
    have e : o * v * o⁻¹ = (v₀ : G) := by rw [hvdef]; group
    rw [e]
    exact hv₀V
  have hvA : ∀ u ∈ A, u * v = v * u := fun u hu => hoc u hu v hvconj
  have hπo : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨o, hoX⟩ = 1 :=
    (mem_glaPPrimeCoreOf_iff hoX).1 ho
  have hvw : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨v, hvX⟩ = w := by
    have e : (⟨v, hvX⟩ : ↥X) = (⟨o, hoX⟩ : ↥X)⁻¹ * v₀ * ⟨o, hoX⟩ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv, hπo, inv_one, one_mul, mul_one, ← hv₀w]
  have hVo3 : IsPGroup 3 ↥(GLBConj o V) := hV3.map _
  have hVoX : GLBConj o V ≤ X := by
    intro z hz
    rw [mem_gLBConj] at hz
    have := X.mul_mem (X.mul_mem (X.inv_mem hoX) ((hVH.trans hHX) hz)) hoX
    simpa [mul_assoc] using this
  have hinj := injective_barX_comp hp3 hVo3 hVoX
  have hv3 : v ^ 3 = 1 := by
    have hv3mem : v ^ 3 ∈ GLBConj o V := (GLBConj o V).pow_mem hvconj 3
    have h1 : ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp ((GLBConj o V).subgroupOf X).subtype)
        ⟨⟨v ^ 3, X.pow_mem hvX 3⟩, Subgroup.mem_subgroupOf.2 hv3mem⟩ =
        ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp ((GLBConj o V).subgroupOf X).subtype) 1 := by
      rw [map_one]
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨v ^ 3, X.pow_mem hvX 3⟩ = 1
      have e : (⟨v ^ 3, X.pow_mem hvX 3⟩ : ↥X) = (⟨v, hvX⟩ : ↥X) ^ 3 := Subtype.ext (by simp)
      rw [e, map_pow, hvw, hw3]
    have h2 := hinj h1
    have h3 := congrArg (fun z => ((z : ↥X) : G)) (congrArg Subtype.val h2)
    simpa using h3
  have hVel : IsElemAbelian 3 (Subgroup.zpowers v) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
      show (a : G) * b = b * a
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow_self v i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv3, one_zpow]
  have hAV : A ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_left (hvA u hu).symm i).eq
  have hE := isElemAbelian_sup_of_commute hAel hVel hAV
  have hEq := hSC.2.2 (A ⊔ Subgroup.zpowers v) le_top hE le_sup_left
  have hvA' : v ∈ A := by
    have : v ∈ A ⊔ Subgroup.zpowers v := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
    rwa [hEq] at this
  apply hwA
  rw [← hvw]
  exact ⟨⟨v, hvX⟩, Subgroup.mem_subgroupOf.2 hvA', rfl⟩

theorem mem_normalizer_kx {J : Subgroup G} {x b : G} (hbX : b ∈ Cg x)
    (hbJ : b ∈ Subgroup.normalizer (J : Set G)) :
    b ∈ Subgroup.normalizer (Kx 3 J x : Set G) := by
  have key : ∀ c ∈ Cg x, c ∈ Subgroup.normalizer (J : Set G) → GLBConj c (Kx 3 J x) ≤ Kx 3 J x := by
    intro c hcX hcJ
    have hcL : c⁻¹ ∈ Subgroup.normalizer (GLAPLayer 3 (Cg x) : Set G) :=
      Lemma1245.mem_normalizer_glaPLayer' (Subgroup.le_normalizer ((Cg x).inv_mem hcX))
    unfold Kx
    rw [GLBConj, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun g hg => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← GLBConj, gLBConj_gLBConj]
    have hg' : c⁻¹ * g * c⁻¹⁻¹ ∈ GLAPLayer 3 (Cg x) := (Subgroup.mem_normalizer_iff.1 hcL g).1 hg
    have e : GLBConj (g * c) J = GLBConj (c⁻¹ * g * c⁻¹⁻¹) J := by
      calc GLBConj (g * c) J = GLBConj (c * (c⁻¹ * g * c⁻¹⁻¹)) J := by congr 1; group
        _ = GLBConj (c⁻¹ * g * c⁻¹⁻¹) (GLBConj c J) := (gLBConj_gLBConj _ _ _).symm
        _ = GLBConj (c⁻¹ * g * c⁻¹⁻¹) J := by rw [gLBConj_eq_of_mem_normalizer hcJ]
    rw [e]
    exact le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (Cg x)) => GLBConj g J) _ hg'
  have h1 := key b hbX hbJ
  have h2 := key b⁻¹ ((Cg x).inv_mem hbX) (Subgroup.inv_mem _ hbJ)
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm h1 ?_
  have h3 := gLBConj_mono b h2
  rwa [gLBConj_gLBConj_inv] at h3

theorem mem_zpowers_of_pow_three {y v : G} (hy3 : y ^ 3 = 1) (hv : v ∈ Subgroup.zpowers y) :
    v = 1 ∨ v = y ∨ v = y * y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
  have hy3' : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy3
  have hred : y ^ k = y ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, hy3', one_zpow, mul_one]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  rw [hred]
  interval_cases (k % 3)
  · left; simp
  · right; left; simp
  · right; right
    rw [show (2 : ℤ) = 1 + 1 by norm_num, zpow_add, zpow_one]

theorem gLBConj_eq_of_acts_inner {X I : Subgroup G} (hI : GLAPComponent 3 X I) {c : G} (hc : c ∈ X)
    {sb : ↥X ⧸ GLAPPrimeCore 3 ↥X} (hsb : sb ∈ barX 3 X I)
    (hact : ∀ z ∈ barX 3 X I, QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨c, hc⟩ * z *
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨c, hc⟩)⁻¹ = sb * z * sb⁻¹) :
    GLBConj c I = I := by
  set cb := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨c, hc⟩ : ↥X) with hcb
  have hXc : GLBConj c X = X := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hc)
  have hIc : GLAPComponent 3 X (GLBConj c I) := by
    have := glaPComponent_gLBConj hI c
    rwa [hXc] at this
  have hbar : barX 3 X (GLBConj c I) = barX 3 X I := by
    ext z
    rw [mem_barX_gLBConj hI.1 hc z]
    constructor
    · intro hz
      have hu : sb⁻¹ * (cb * z * cb⁻¹) * sb ∈ barX 3 X I :=
        (barX 3 X I).mul_mem ((barX 3 X I).mul_mem ((barX 3 X I).inv_mem hsb) hz) hsb
      have h1 := hact _ hu
      have e : z = sb⁻¹ * (cb * z * cb⁻¹) * sb := by
        have h2 : cb * (sb⁻¹ * (cb * z * cb⁻¹) * sb) * cb⁻¹ = cb * z * cb⁻¹ := by
          rw [h1]; group
        calc z = cb⁻¹ * (cb * z * cb⁻¹) * cb := by group
          _ = cb⁻¹ * (cb * (sb⁻¹ * (cb * z * cb⁻¹) * sb) * cb⁻¹) * cb := by rw [h2]
          _ = sb⁻¹ * (cb * z * cb⁻¹) * sb := by group
      rw [e]
      exact hu
    · intro hz
      rw [hact z hz]
      exact (barX 3 X I).mul_mem ((barX 3 X I).mul_mem hsb hz) ((barX 3 X I).inv_mem hsb)
  exact glaPComponent_unique hIc hI hbar

end UniqHelpers

theorem uniqClaim_of_inputs (h122 : Lemma122_i_iiStatement) (h123 : Lemma123Statement)
    (h117 : Prop117_cex_falseStatement) (h104ii : Lemma104_iiStatement)
    (h104iii : Lemma104_iiiStatement) (h104iv : Lemma104_ivStatement) (hI7 : Input7_L34)
    (hFix : InputL34Fix3) : Lemma1245.UniqClaim := by
  intro G _ _ m B M E A a h K hK hK3 hKM hA0 hAN hKt hcov x hx hx1 hKxc hJcov I hI hIt hIc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  by_contra hne
  have hA4 : CFSG.Open.pRank 3 A = 4 :=
    Lemma1245.pRank_eq_four_of_inputs h122 h123 h117 h104ii h104iii h104iv h hK hK3 hKM
  obtain ⟨hdec, hdisjSF, hS9, hF9⟩ :=
    Lemma1245.lemma124_print_i_of_inputs h122 h123 h117 h104ii h104iii h104iv hI7 h hK hK3 hKM hA0 hAN hKt
  set J := Lemma1245.JJ A K with hJdef
  set F := Lemma1245.FF A K with hFdef
  set L := Kx 3 J x with hLdef
  set X := Cg x with hXdef
  set S := A ⊓ J with hSdef
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hA3 : IsPGroup 3 ↥A := Lemma124.isPGroup_three_of_isElemAbelian hAel
  have hSC : IsSCp 3 ⊤ A := (h104ii h.toSec11.toSec10Fails h.pair).2
  have hAcard : Nat.card A = 81 := by
    rw [Lemma124.card_eq_of_pRank_four hAel hA4]
    norm_num
  have hFA : F ≤ A := inf_le_right
  have hSA : S ≤ A := inf_le_left
  have hxA : x ∈ A := hFA hx
  have hcommA : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc =>
    CFSG.Open.IsElemAbelian.comm hAel hb hc
  have hAX : A ≤ X := fun b hb => Subgroup.mem_centralizer_iff.2 fun z hz => by
    rw [Set.mem_singleton_iff.1 hz]
    exact hcommA x hxA b hb
  have hxX : x ∈ X := hAX hxA
  have hx3 : x ^ 3 = 1 := hAel.2 x hxA
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxcen : ∀ c ∈ X, x * c = c * x := fun c hc =>
    Subgroup.mem_centralizer_iff.1 hc x (Set.mem_singleton x)
  obtain ⟨y, hyF, hyx⟩ : ∃ y ∈ F, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have hc := Subgroup.card_le_of_le (fun f hf => hcon f hf : F ≤ Subgroup.zpowers x)
    rw [hF9, Nat.card_zpowers, hxo] at hc
    omega
  have hyA : y ∈ A := hFA hyF
  have hy3 : y ^ 3 = 1 := hAel.2 y hyA
  have hy1 : y ≠ 1 := fun h1 => hyx (h1 ▸ Subgroup.one_mem _)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyX : y ∈ X := hAX hyA
  have hzx : Subgroup.zpowers x ≤ F := Subgroup.zpowers_le.2 hx
  have hzy : Subgroup.zpowers y ≤ F := Subgroup.zpowers_le.2 hyF
  have hcxy : ∀ u ∈ Subgroup.zpowers x, ∀ v ∈ Subgroup.zpowers y, u * v = v * u :=
    fun u hu v hv => hcommA u (hFA (hzx hu)) v (hFA (hzy hv))
  have hxy_disj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    by_contra hz1
    have hzy' : Subgroup.zpowers z = Subgroup.zpowers y :=
      Lemma1112b.zpowers_eq_of_card_three (by rw [Nat.card_zpowers, hyo]) hz.2 hz1
    apply hyx
    have : y ∈ Subgroup.zpowers z := hzy' ▸ Subgroup.mem_zpowers y
    exact (Subgroup.zpowers_le.2 hz.1) this
  have hFxy : F = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ F := sup_le hzx hzy
    have hcard : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) = 9 := by
      rw [Lemma124.card_eq_mul_of_sup_eq hcxy rfl hxy_disj, Nat.card_zpowers, Nat.card_zpowers, hxo, hyo]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hF9])).symm
  have hcSF : ∀ s ∈ S, ∀ f ∈ F, s * f = f * s := fun s hs f hf =>
    hcommA s (Subgroup.mem_inf.1 hs).1 f (hFA hf)
  have hdecA : ∀ b ∈ A, ∃ s ∈ S, ∃ u ∈ Subgroup.zpowers x, ∃ v ∈ Subgroup.zpowers y,
      s * (u * v) = b := by
    intro b hb
    have hb' : b ∈ S ⊔ F := hdec ▸ hb
    obtain ⟨s, hs, f, hf, rfl⟩ := Lemma124.exists_mul_of_mem_sup hcSF hb'
    rw [hFxy] at hf
    obtain ⟨u, hu, v, hv, rfl⟩ := Lemma124.exists_mul_of_mem_sup hcxy hf
    exact ⟨s, hs, u, hu, v, hv, rfl⟩
  set π : ↥X →* ↥X ⧸ GLAPPrimeCore 3 ↥X := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hπ
  have hπinj : ∀ b (hb : b ∈ A), π ⟨b, hAX hb⟩ = 1 → b = 1 := by
    intro b hb h1
    have hi := injective_barX_comp hp3 hA3 hAX
    have h2 : ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (A.subgroupOf X).subtype)
        ⟨⟨b, hAX hb⟩, hb⟩ =
        ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (A.subgroupOf X).subtype) 1 := by
      rw [map_one]
      exact h1
    have h3 := congrArg (fun z => ((z : ↥X) : G)) (congrArg Subtype.val (hi h2))
    simpa using h3
  have hπmul : ∀ b (hb : b ∈ A), ∃ s ∈ S, ∃ u ∈ Subgroup.zpowers x, ∃ v ∈ Subgroup.zpowers y,
      ∃ (hsX : s ∈ X) (huX : u ∈ X) (hvX : v ∈ X),
        π ⟨b, hAX hb⟩ = π ⟨s, hsX⟩ * (π ⟨u, huX⟩ * π ⟨v, hvX⟩) := by
    intro b hb
    obtain ⟨s, hs, u, hu, v, hv, hsuv⟩ := hdecA b hb
    have hsX : s ∈ X := hAX (Subgroup.mem_inf.1 hs).1
    have huX : u ∈ X := hAX (hFA (hzx hu))
    have hvX : v ∈ X := hAX (hFA (hzy hv))
    refine ⟨s, hs, u, hu, v, hv, hsX, huX, hvX, ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hsuv.symm
  have hJL : J ≤ L := Sec12b.le_kx x J
  have hJX : J ≤ X := hJL.trans hKxc.1
  have hLJ : barX 3 X L ≤ barX 3 X J := by
    rintro z ⟨k, hk, rfl⟩
    have hkL : (k : G) ∈ L := hk
    obtain ⟨j, hj, o, ho, hjo⟩ := Sec12b.mem_mul_glaPPrimeCoreOf_of_barX hJL hJcov hkL
    have hoX : o ∈ GLAPPrimeCoreOf 3 X := glaPPrimeCoreOf_le_of_isSubnormal hp3 hKxc.2.1 ho
    refine ⟨⟨j, hJX hj⟩, (Subgroup.mem_subgroupOf.2 hj), ?_⟩
    show QuotientGroup.mk' _ (⟨j, hJX hj⟩ : ↥X) = QuotientGroup.mk' _ (⟨(k : G), k.2⟩ : ↥X)
    rw [mk_eq_mk_iff_mem (hJX hj) k.2, hjo]
    simpa using hoX
  have hJK : J ≤ K := (Sec12b.layer_le 3 _).trans inf_le_left
  obtain ⟨eK, -⟩ := Lemma1245.exists_barOf_equiv_of_cover (p := 3) hp3 hJK hcov
  obtain ⟨eX, -⟩ := Lemma1245.exists_barOf_equiv_of_cover (p := 3) hp3 hJL hJcov
  have hLc : Subgroup.center (barOf 3 L) = ⊥ :=
    Lemma1245.center_eq_bot_of_equiv (eX.symm.trans eK) hKt
  have hLc' : Subgroup.center ↥(barX 3 X L) = ⊥ := center_barX_eq_bot hKxc hLc
  have hIc' : Subgroup.center ↥(barX 3 X I) = ⊥ := center_barX_eq_bot hI hIc
  have hIL34 : IsLThreeFour ↥(barX 3 X I) :=
    Lemma1245.isLThreeFour_congr
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barXEquiv hp3 hI.2.1)
      (Lemma1245.isLThreeFour_of_center_bot hIt hIc)
  have hπx : ∀ u ∈ Subgroup.zpowers x, ∀ (huX : u ∈ X) (z : ↥X ⧸ GLAPPrimeCore 3 ↥X),
      π ⟨u, huX⟩ * z = z * π ⟨u, huX⟩ := by
    intro u hu huX z
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ z
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((Commute.zpow_left (hxcen c c.2) i).eq)
  have hπS : ∀ s (hs : s ∈ S) (hsX : s ∈ X), π ⟨s, hsX⟩ ∈ barX 3 X L := fun s hs hsX =>
    ⟨⟨s, hsX⟩, Subgroup.mem_subgroupOf.2 (hJL (Subgroup.mem_inf.1 hs).2), rfl⟩
  set yb := π ⟨y, hyX⟩ with hyb
  have hπy : ∀ v ∈ Subgroup.zpowers y, ∀ hvX : v ∈ X, π ⟨v, hvX⟩ ∈ Subgroup.zpowers yb := by
    intro v hv hvX
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [hyb, ← map_zpow]
    rfl
  have hyb3 : yb * yb * yb = 1 := by
    rw [hyb, ← map_mul, ← map_mul]
    have : (⟨y, hyX⟩ : ↥X) * ⟨y, hyX⟩ * ⟨y, hyX⟩ = 1 := Subtype.ext (by
      show y * y * y = 1
      rw [← hy3, pow_three, mul_assoc])
    rw [this, map_one]
  have hAL : ∀ b ∈ A, b ∈ Subgroup.normalizer (L : Set G) := fun b hb =>
    mem_normalizer_kx (hAX hb) (Lemma1245.mem_normalizer_JJ (hAN hb)
      (Subgroup.mem_centralizer_iff.2 fun f hf => hcommA f (hFA hf) b hb))
  by_cases hyI : y ∈ Subgroup.normalizer (I : Set G)
  ·
    have hyIb : yb ∈ Subgroup.normalizer (barX 3 X I : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have h1 := mem_barX_gLBConj hI.1 hyX z
      rw [mem_normalizer_iff_gLBConj_eq.1 hyI] at h1
      exact h1
    set φ : MulAut ↥(barX 3 X I) := (barX 3 X I).normalizerMonoidHom ⟨yb, hyIb⟩ with hφ
    have hφ3 : φ ^ 3 = 1 := by
      rw [hφ, ← map_pow]
      have : (⟨yb, hyIb⟩ : ↥(Subgroup.normalizer (barX 3 X I : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))) ^ 3
          = 1 := Subtype.ext (by
            show yb ^ 3 = 1
            rw [← hyb3, pow_three, mul_assoc])
      rw [this, map_one]
    set Z : Subgroup ↥(barX 3 X I) := (barX 3 X A).subgroupOf (barX 3 X I) with hZ
    set D : Subgroup G := A ⊓ ((barX 3 X I).comap π).map X.subtype with hD
    have hDA : D ≤ A := inf_le_left
    have hSxA : S ⊔ Subgroup.zpowers x ≤ A := sup_le hSA (hzx.trans hFA)
    have hDS : D ⊓ (S ⊔ Subgroup.zpowers x) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro b hb
      obtain ⟨⟨hbA, hbI⟩, hbSx⟩ := hb
      obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.1 hbI
      obtain ⟨s, hs, u, hu, rfl⟩ := Lemma124.exists_mul_of_mem_sup
        (fun s hs u hu => hcSF s hs u (hzx hu)) hbSx
      have hsA : s ∈ A := (Subgroup.mem_inf.1 hs).1
      have hsX : s ∈ X := hAX hsA
      have huX : u ∈ X := hAX (hFA (hzx hu))
      have hcsu : c = ⟨s, hsX⟩ * ⟨u, huX⟩ := Subtype.ext hcb
      have hπI : π ⟨s, hsX⟩ * π ⟨u, huX⟩ ∈ barX 3 X I := by
        rw [← map_mul, ← hcsu]
        exact hc
      have hs1 : π ⟨s, hsX⟩ = 1 := by
        have hmem : (⟨π ⟨s, hsX⟩, hπS s hs hsX⟩ : ↥(barX 3 X L)) ∈
            Subgroup.center ↥(barX 3 X L) := by
          rw [Subgroup.mem_center_iff]
          intro z
          apply Subtype.ext
          show (z : ↥X ⧸ GLAPPrimeCore 3 ↥X) * π ⟨s, hsX⟩ = π ⟨s, hsX⟩ * z
          have h1 := commute_of_glaPComponent_ne hI hKxc hne hπI z.2
          have h2 := hπx u hu huX (z : ↥X ⧸ GLAPPrimeCore 3 ↥X)
          have h5 : π ⟨s, hsX⟩ * z * π ⟨u, huX⟩ = z * π ⟨s, hsX⟩ * π ⟨u, huX⟩ := by
            calc π ⟨s, hsX⟩ * z * π ⟨u, huX⟩ = π ⟨s, hsX⟩ * (z * π ⟨u, huX⟩) := by group
              _ = π ⟨s, hsX⟩ * (π ⟨u, huX⟩ * z) := by rw [h2]
              _ = (π ⟨s, hsX⟩ * π ⟨u, huX⟩) * z := by group
              _ = z * (π ⟨s, hsX⟩ * π ⟨u, huX⟩) := h1
              _ = z * π ⟨s, hsX⟩ * π ⟨u, huX⟩ := by group
          exact (mul_right_cancel h5).symm
        rw [hLc', Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      have hs1' : s = 1 := hπinj s hsA hs1
      subst hs1'
      have hu1 : π ⟨u, huX⟩ = 1 := by
        have hπI' : π ⟨u, huX⟩ ∈ barX 3 X I := by
          rw [hs1, one_mul] at hπI
          exact hπI
        have hmem : (⟨π ⟨u, huX⟩, hπI'⟩ : ↥(barX 3 X I)) ∈ Subgroup.center ↥(barX 3 X I) := by
          rw [Subgroup.mem_center_iff]
          intro z
          apply Subtype.ext
          exact (hπx u hu huX (z : ↥X ⧸ GLAPPrimeCore 3 ↥X)).symm
        rw [hIc', Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      rw [one_mul]
      exact hπinj u (hFA (hzx hu)) hu1
    have hSx27 : Nat.card (S ⊔ Subgroup.zpowers x : Subgroup G) = 27 := by
      have hdj : S ⊓ Subgroup.zpowers x = ⊥ :=
        le_bot_iff.1 (hdisjSF ▸ inf_le_inf_left S hzx)
      rw [Lemma124.card_eq_mul_of_sup_eq (fun s hs u hu => hcSF s hs u (hzx hu)) rfl hdj,
        hS9, Nat.card_zpowers, hxo]
    have hD3 : Nat.card D ≤ 3 := by
      have hmul := Lemma124.card_eq_mul_of_sup_eq
        (fun b hb c hc => hcommA b (hDA hb) c (hSxA hc)) rfl hDS
      have hle : Nat.card (D ⊔ (S ⊔ Subgroup.zpowers x) : Subgroup G) ≤ 81 := by
        have := Subgroup.card_le_of_le (sup_le hDA hSxA)
        rwa [hAcard] at this
      rw [hmul, hSx27] at hle
      omega
    have hZ3 : Nat.card Z ≤ 3 := by
      refine le_trans ?_ hD3
      have hsurj : ∀ z : ↥Z, ∃ d : ↥D, ((z : ↥(barX 3 X I)) : ↥X ⧸ GLAPPrimeCore 3 ↥X) =
          π ⟨d, hAX (hDA d.2)⟩ := by
        intro z
        obtain ⟨c, hcA, hc⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 z.2)
        have hcA' : (c : G) ∈ A := hcA
        refine ⟨⟨c, hcA', Subgroup.mem_map.2 ⟨c, ?_, rfl⟩⟩, ?_⟩
        · show π c ∈ barX 3 X I
          rw [show π c = QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) c from rfl, hc]
          exact (z : ↥(barX 3 X I)).2
        · exact hc.symm
      choose f hf using hsurj
      refine Nat.card_le_card_of_injective f fun z₁ z₂ h12 => ?_
      apply Subtype.ext
      apply Subtype.ext
      rw [hf z₁, hf z₂, h12]
    obtain ⟨w, hwo, hwφ, hwZ⟩ := hFix ↥(barX 3 X I) hIL34 φ hφ3 Z hZ3
    have hwyb : yb * (w : ↥X ⧸ GLAPPrimeCore 3 ↥X) * yb⁻¹ = w := by
      have := congrArg Subtype.val hwφ
      rw [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe] at this
      exact this
    refine false_of_commute_of_isSCp hAX hAel hSC (w := (w : ↥X ⧸ GLAPPrimeCore 3 ↥X)) ?_ ?_ ?_
    · have := pow_orderOf_eq_one w
      rw [hwo] at this
      exact congrArg Subtype.val this
    · intro hwA
      exact hwZ (Subgroup.mem_subgroupOf.2 hwA)
    · intro z hz
      obtain ⟨c, hcA, rfl⟩ := hz
      have hcA' : (c : G) ∈ A := hcA
      obtain ⟨s, hs, u, hu, v, hv, hsX, huX, hvX, he⟩ := hπmul c hcA'
      have hc' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) c = π ⟨(c : G), hAX hcA'⟩ := rfl
      rw [hc', he]
      have h1 : Commute (w : ↥X ⧸ GLAPPrimeCore 3 ↥X) (π ⟨s, hsX⟩) :=
        commute_of_glaPComponent_ne hI hKxc hne w.2 (hπS s hs hsX)
      have h2 : Commute (π ⟨u, huX⟩) (w : ↥X ⧸ GLAPPrimeCore 3 ↥X) :=
        hπx u hu huX (w : ↥X ⧸ GLAPPrimeCore 3 ↥X)
      have hcy : Commute yb (w : ↥X ⧸ GLAPPrimeCore 3 ↥X) := by
        show yb * w = w * yb
        calc yb * (w : ↥X ⧸ GLAPPrimeCore 3 ↥X) = (yb * w * yb⁻¹) * yb := by group
          _ = w * yb := by rw [hwyb]
      have h3 : Commute (π ⟨v, hvX⟩) (w : ↥X ⧸ GLAPPrimeCore 3 ↥X) := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hπy v hv hvX)
        rw [← hk]
        exact hcy.zpow_left k
      exact (h1.symm.mul_left (h2.mul_left h3)).eq
  ·
    have hXy : GLBConj y X = X := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hyX)
    have hyyX : y * y ∈ X := X.mul_mem hyX hyX
    have hXyy : GLBConj (y * y) X = X :=
      gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hyyX)
    have hI2 : GLAPComponent 3 X (GLBConj y I) := by
      have := glaPComponent_gLBConj hI y
      rwa [hXy] at this
    have hI3 : GLAPComponent 3 X (GLBConj (y * y) I) := by
      have := glaPComponent_gLBConj hI (y * y)
      rwa [hXyy] at this
    have hGy : GLBConj y I ≠ I := fun he => hyI (mem_normalizer_iff_gLBConj_eq.2 he)
    have hGyy : GLBConj (y * y) I ≠ I := by
      intro he
      apply hyI
      have hyy : y * y ∈ Subgroup.normalizer (I : Set G) := mem_normalizer_iff_gLBConj_eq.2 he
      have hy4 : (y * y) * (y * y) = y := by
        calc (y * y) * (y * y) = (y * y * y) * y := by group
          _ = y := by rw [show y * y * y = y ^ 3 by rw [pow_three, mul_assoc], hy3, one_mul]
      rw [← hy4]
      exact Subgroup.mul_mem _ hyy hyy
    have hG23 : GLBConj y I ≠ GLBConj (y * y) I := by
      intro he
      apply hGy
      have := congrArg (GLBConj y⁻¹) he
      rw [gLBConj_inv_gLBConj, gLBConj_gLBConj] at this
      rw [show y * y * y⁻¹ = y by group] at this
      exact this.symm
    have hLy : ∀ c ∈ A, GLBConj c L = L := fun c hc => mem_normalizer_iff_gLBConj_eq.1 (hAL c hc)
    have hI2L : GLBConj y I ≠ L := by
      intro he
      apply hne
      have := congrArg (GLBConj y⁻¹) he
      rwa [gLBConj_inv_gLBConj, hLy y⁻¹ (A.inv_mem hyA)] at this
    have hI3L : GLBConj (y * y) I ≠ L := by
      intro he
      apply hne
      have := congrArg (GLBConj (y * y)⁻¹) he
      rwa [gLBConj_inv_gLBConj, hLy _ (A.inv_mem (A.mul_mem hyA hyA))] at this
    obtain ⟨s₀, hs₀o, -, -⟩ := hFix ↥(barX 3 X I) hIL34 1 (one_pow 3) ⊥ (by simp)
    set sb : ↥X ⧸ GLAPPrimeCore 3 ↥X := (s₀ : ↥X ⧸ GLAPPrimeCore 3 ↥X) with hsb
    have hsbI : sb ∈ barX 3 X I := s₀.2
    have hsb3 : sb ^ 3 = 1 := by
      have := pow_orderOf_eq_one s₀
      rw [hs₀o] at this
      exact congrArg Subtype.val this
    set s2 := yb⁻¹ * sb * yb with hs2def
    set s3 := yb⁻¹ * s2 * yb with hs3def
    have hs2 : s2 ∈ barX 3 X (GLBConj y I) := by
      rw [mem_barX_gLBConj hI.1 hyX]
      have e : π ⟨y, hyX⟩ * s2 * (π ⟨y, hyX⟩)⁻¹ = sb := by
        rw [← hyb, hs2def]
        group
      rw [e]
      exact hsbI
    have hs3 : s3 ∈ barX 3 X (GLBConj (y * y) I) := by
      rw [← gLBConj_gLBConj, mem_barX_gLBConj hI2.1 hyX]
      have e : π ⟨y, hyX⟩ * s3 * (π ⟨y, hyX⟩)⁻¹ = s2 := by
        rw [← hyb, hs3def]
        group
      rw [e]
      exact hs2
    have c12 : Commute sb s2 := commute_of_glaPComponent_ne hI hI2 (Ne.symm hGy) hsbI hs2
    have c13 : Commute sb s3 := commute_of_glaPComponent_ne hI hI3 (Ne.symm hGyy) hsbI hs3
    have c23 : Commute s2 s3 := commute_of_glaPComponent_ne hI2 hI3 hG23 hs2 hs3
    set t := sb * s2 * s3 with htdef
    have hs4 : yb⁻¹ * s3 * yb = sb := by
      have e : yb⁻¹ * s3 * yb = (yb * yb * yb)⁻¹ * sb * (yb * yb * yb) := by
        rw [hs3def, hs2def]
        group
      rw [e, hyb3, inv_one, one_mul, mul_one]
    have e1 : yb⁻¹ * t * yb = s2 * s3 * sb := by
      calc yb⁻¹ * t * yb = (yb⁻¹ * sb * yb) * (yb⁻¹ * s2 * yb) * (yb⁻¹ * s3 * yb) := by
            rw [htdef]; group
        _ = s2 * s3 * sb := by rw [← hs2def, ← hs3def, hs4]
    have e2 : s2 * s3 * sb = t := by
      calc s2 * s3 * sb = s2 * (s3 * sb) := by group
        _ = s2 * (sb * s3) := by rw [c13.eq]
        _ = (s2 * sb) * s3 := by group
        _ = (sb * s2) * s3 := by rw [c12.eq]
    have hty : Commute yb t := by
      show yb * t = t * yb
      calc yb * t = yb * (yb⁻¹ * t * yb) := by rw [e1, e2]
        _ = t * yb := by group
    have hs2' : s2 ^ 3 = 1 := by
      have e : s2 ^ 3 = yb⁻¹ * sb ^ 3 * yb := by
        have := conj_pow (a := yb⁻¹) (b := sb) (i := 3)
        rwa [inv_inv] at this
      rw [e, hsb3]
      group
    have hs3' : s3 ^ 3 = 1 := by
      have e : s3 ^ 3 = yb⁻¹ * s2 ^ 3 * yb := by
        have := conj_pow (a := yb⁻¹) (b := s2) (i := 3)
        rwa [inv_inv] at this
      rw [e, hs2']
      group
    have ht3 : t ^ 3 = 1 := by
      rw [htdef, (c13.mul_left c23).mul_pow, c12.mul_pow, hsb3, hs2', hs3']
      group
    have htcomm : ∀ z ∈ barX 3 X A, z * t = t * z := by
      intro z hz
      obtain ⟨c, hcA, rfl⟩ := hz
      have hcA' : (c : G) ∈ A := hcA
      obtain ⟨s, hs, u, hu, v, hv, hsX, huX, hvX, he⟩ := hπmul c hcA'
      have hc' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) c = π ⟨(c : G), hAX hcA'⟩ := rfl
      rw [hc', he]
      have hsL := hπS s hs hsX
      have d1 : Commute sb (π ⟨s, hsX⟩) := commute_of_glaPComponent_ne hI hKxc hne hsbI hsL
      have d2 : Commute s2 (π ⟨s, hsX⟩) := commute_of_glaPComponent_ne hI2 hKxc hI2L hs2 hsL
      have d3 : Commute s3 (π ⟨s, hsX⟩) := commute_of_glaPComponent_ne hI3 hKxc hI3L hs3 hsL
      have hst : Commute (π ⟨s, hsX⟩) t := ((d1.mul_left d2).mul_left d3).symm
      have hut : Commute (π ⟨u, huX⟩) t := hπx u hu huX t
      have hvt : Commute (π ⟨v, hvX⟩) t := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hπy v hv hvX)
        rw [← hk]
        exact hty.zpow_left k
      exact (hst.mul_left (hut.mul_left hvt)).eq
    have htA : t ∉ barX 3 X A := by
      intro htA
      obtain ⟨c, hcA, hct⟩ := htA
      have hcA' : (c : G) ∈ A := hcA
      obtain ⟨s, hs, u, hu, v, hv, hsX, huX, hvX, he⟩ := hπmul c hcA'
      have hc' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) c = π ⟨(c : G), hAX hcA'⟩ := rfl
      rw [hc', he] at hct
      set q := π ⟨s, hsX⟩ * π ⟨u, huX⟩ with hq
      have hqI : ∀ z ∈ barX 3 X I, q * z = z * q := by
        intro z hz
        have d1 : Commute z (π ⟨s, hsX⟩) :=
          commute_of_glaPComponent_ne hI hKxc hne hz (hπS s hs hsX)
        have d2 : Commute (π ⟨u, huX⟩) z := hπx u hu huX z
        exact ((d1.symm).mul_left d2).eq
      have htI : ∀ z ∈ barX 3 X I, t * z * t⁻¹ = sb * z * sb⁻¹ := by
        intro z hz
        have e2' : Commute z s2 := commute_of_glaPComponent_ne hI hI2 (Ne.symm hGy) hz hs2
        have e3' : Commute z s3 := commute_of_glaPComponent_ne hI hI3 (Ne.symm hGyy) hz hs3
        have f1 : s3 * z * s3⁻¹ = z := by rw [← e3'.eq]; group
        have f2 : s2 * z * s2⁻¹ = z := by rw [← e2'.eq]; group
        calc t * z * t⁻¹ = sb * (s2 * (s3 * z * s3⁻¹) * s2⁻¹) * sb⁻¹ := by rw [htdef]; group
          _ = sb * z * sb⁻¹ := by rw [f1, f2]
      have hvI : ∀ z ∈ barX 3 X I, π ⟨v, hvX⟩ * z * (π ⟨v, hvX⟩)⁻¹ = sb * z * sb⁻¹ := by
        intro z hz
        have hv' : π ⟨v, hvX⟩ = q⁻¹ * t := by
          rw [← hct, hq]
          group
        have hzI : sb * z * sb⁻¹ ∈ barX 3 X I :=
          (barX 3 X I).mul_mem ((barX 3 X I).mul_mem hsbI hz) ((barX 3 X I).inv_mem hsbI)
        have hc := hqI _ hzI
        rw [hv']
        calc q⁻¹ * t * z * (q⁻¹ * t)⁻¹ = q⁻¹ * (t * z * t⁻¹) * q := by group
          _ = q⁻¹ * (sb * z * sb⁻¹) * q := by rw [htI z hz]
          _ = q⁻¹ * (q * (sb * z * sb⁻¹)) := by rw [mul_assoc, ← hc]
          _ = sb * z * sb⁻¹ := by group
      rcases mem_zpowers_of_pow_three hy3 hv with rfl | rfl | rfl
      ·
        have hv1 : π ⟨1, hvX⟩ = 1 := by
          rw [show (⟨1, hvX⟩ : ↥X) = 1 from rfl, map_one]
        have hcen : (⟨sb, hsbI⟩ : ↥(barX 3 X I)) ∈ Subgroup.center ↥(barX 3 X I) := by
          rw [Subgroup.mem_center_iff]
          intro z
          apply Subtype.ext
          have hz := hvI z z.2
          rw [hv1, one_mul, inv_one, mul_one] at hz
          show (z : ↥X ⧸ GLAPPrimeCore 3 ↥X) * sb = sb * z
          calc (z : ↥X ⧸ GLAPPrimeCore 3 ↥X) * sb = (sb * z * sb⁻¹) * sb := by rw [← hz]
            _ = sb * z := by group
        rw [hIc', Subgroup.mem_bot] at hcen
        have hs₀1 : s₀ = 1 := Subtype.ext (congrArg Subtype.val hcen)
        rw [hs₀1, orderOf_one] at hs₀o
        norm_num at hs₀o
      · exact hGy (gLBConj_eq_of_acts_inner hI hvX hsbI hvI)
      · exact hGyy (gLBConj_eq_of_acts_inner hI hvX hsbI hvI)
    exact false_of_commute_of_isSCp hAX hAel hSC ht3 htA htcomm

section NormHelpers

variable {G : Type} [Group G] [Finite G]

theorem pRank_mulAut_le_two_of_modCenter {Y : Type} [Group Y] [Finite Y] (hperf : commutator Y = ⊤)
    (h : IsLThreeFour (Y ⧸ Subgroup.center Y)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y)) ≤ 2 :=
  (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) (quotientCenterAut' Y)
    (quotientCenterAut'_injective hperf)).trans (pRank_mulAut_le_two_of_isLThreeFour h)

theorem le_M_of_rank_five (h104ii : Lemma104_iiStatement) (h104iii : Lemma104_iiiStatement)
    (h104iv : Lemma104_ivStatement) (h111 : Prop111Statement)
    {m : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m 3 B M E A a)
    (hk : CFSG.Open.pRank 3 (E ⊓ A) = 2) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1)
    {I : Subgroup G} (hI : GLAPComponent 3 (Cg x) I)
    (hIt : IsLThreeFour (barOf 3 I ⧸ Subgroup.center (barOf 3 I)))
    {D : Subgroup G} (hDel : IsElemAbelian 3 D) (hD5 : 3 ^ 5 ≤ Nat.card D) (hDC : D ≤ Cg x)
    (hDA0 : D ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G)) : I ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hNA0 : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M :=
    le_trans (le_sSup ⟨E ⊓ A, inf_le_left, le_of_eq hk.symm, rfl⟩ :
      Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ GLBCore 3 2 E) h.pair.1.1.2.clause_d
  have hDM : D ≤ M := hDA0.trans ((Subgroup.centralizer_le_normalizer _).trans hNA0)
  have hcardD : Nat.card D = 3 ^ CFSG.Open.pRank 3 D := Lemma124.card_eq_pow_pRank hDel
  have hr5 : 5 ≤ CFSG.Open.pRank 3 D := by
    rw [hcardD] at hD5
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hD5
  obtain ⟨H5, hH5⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥D) 3 (n := 5)
    (by rw [hcardD]; exact pow_dvd_pow 3 hr5)
  set D5 : Subgroup G := H5.map D.subtype with hD5def
  have hD5D : D5 ≤ D := Subgroup.map_subtype_le _
  have hD5card : Nat.card D5 = 3 ^ 5 := by
    rw [hD5def, Subgroup.card_map_of_injective D.subtype_injective, hH5]
  have hD5el : IsElemAbelian 3 D5 := Lemma124.isElemAbelian_of_le hD5D hDel
  obtain ⟨R, hR, hD5R⟩ := Lemma124.exists_isSylowIn_above_aux (hD5D.trans hDM)
    (Lemma124.isPGroup_three_of_isElemAbelian hD5el)
  obtain ⟨hinD0, -, -⟩ := h104iv h.toSec11.toSec10Fails h.pair hk hR
  obtain ⟨-, -, A', hA'D, hD5A'⟩ := hinD0 D5 ⟨hD5R, hD5el, hD5card⟩
  obtain ⟨Ds, hDDs, hDsmax⟩ := (Set.toFinite {X : Subgroup G | IsElemAbelian 3 X ∧ D ≤ X}).exists_le_maximal
    (a := D) ⟨hDel, le_rfl⟩
  have hDsel : IsElemAbelian 3 Ds := hDsmax.1.1
  have hDsSC : IsSCp 3 ⊤ Ds := ⟨le_top, hDsel, fun X _ hX hDsX =>
    le_antisymm (hDsmax.2 ⟨hX, hDDs.trans hDsX⟩ hDsX) hDsX⟩
  obtain ⟨H3, hH3⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥D5) 3 (n := 3)
    (by rw [hD5card]; exact pow_dvd_pow 3 (by norm_num))
  set D3 : Subgroup G := H3.map D5.subtype with hD3def
  have hD3D5 : D3 ≤ D5 := Subgroup.map_subtype_le _
  have hD3card : Nat.card D3 = 3 ^ 3 := by
    rw [hD3def, Subgroup.card_map_of_injective D5.subtype_injective, hH3]
  have hD3el : IsElemAbelian 3 D3 := Lemma124.isElemAbelian_of_le hD3D5 hD5el
  have hA'el : IsElemAbelian 3 A' := hA'D.1.1.2.1
  have hconn : IsKConnectedIn 3 (CFSG.Open.pRank 3 (E ⊓ A) + 1) ⊤ Ds A' := by
    rw [hk]
    refine ⟨le_top, hDsel, ?_, le_top, hA'el, ?_, Or.inr ⟨D3, D3, ⟨le_top, hD3el, hD3card⟩,
      ⟨le_top, hD3el, hD3card⟩, ?_, Relation.ReflTransGen.refl, ?_⟩⟩
    · calc 3 ^ 3 = Nat.card D3 := hD3card.symm
        _ ≤ Nat.card Ds := Subgroup.card_le_of_le (hD3D5.trans (hD5D.trans hDDs))
    · calc 3 ^ 3 = Nat.card D3 := hD3card.symm
        _ ≤ Nat.card A' := Subgroup.card_le_of_le (hD3D5.trans hD5A')
    · intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact CFSG.Open.IsElemAbelian.comm hDsel (hD3D5.trans (hD5D.trans hDDs) hv) hu
    · intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact CFSG.Open.IsElemAbelian.comm hA'el hv ((hD3D5.trans hD5A') hu)
  have hDsD : inD 3 M Ds := h104iii h.toSec11.toSec10Fails h.pair hDsSC hA'D hconn
  have hnorm : ∀ E' : Subgroup G, E' ≤ D → 3 ≤ CFSG.Open.pRank 3 E' →
      Subgroup.normalizer (E' : Set G) ≤ M := fun E' hE'D hE'3 =>
    le_trans (le_sSup ⟨E', hE'D.trans hDDs, by omega, rfl⟩ :
      Subgroup.normalizer (E' : Set G) ≤ GLBCore 3 2 Ds) hDsD.2.clause_d
  have hD3' : IsPGroup 3 ↥D := Lemma124.isPGroup_three_of_isElemAbelian hDel
  have hK : IsComponentOf (barX 3 (Cg x) I) ⊤ := hI.2.2.1
  have hperf : commutator ↥(barX 3 (Cg x) I) = ⊤ := hK.2.2.1
  have hIt' : IsLThreeFour (↥(barX 3 (Cg x) I) ⧸ Subgroup.center ↥(barX 3 (Cg x) I)) :=
    Lemma1245.isLThreeFour_modCenter_congr (quotEquivBarX hp3 hI.1 hI.2.1) hIt
  have hm2 := pRank_mulAut_le_two_of_modCenter hperf hIt'
  have hrD : CFSG.Open.pRank 3 (barX 3 (Cg x) D) = CFSG.Open.pRank 3 D :=
    rank_barX_of_isPGroup hp3 hD3' hDC
  have hgen := GL83.I_22_5_proved (↥(Cg x) ⧸ GLAPPrimeCore 3 ↥(Cg x)) 3 hp3
    (glaPPrimeCore_quotient_eq_bot hp3) (barX 3 (Cg x) I) hK (barX 3 (Cg x) D)
    (isElemAbelian_barX hDel) (by omega) 3 (by norm_num) (by omega)
  exact le_of_barX_le_glbCore hp3 3 hD3' hDC hI.1 hnorm (h111 h.toSec11 hxA hx1) hgen

theorem isSylowIn_inf_of_isSubnormal {X Q I : Subgroup G} (hQ : IsSylowIn 3 X Q)
    (hI : IsSubnormal I X) : IsSylowIn 3 I (Q ⊓ I) := by
  induction hI with
  | refl => rwa [inf_eq_left.2 hQ.1]
  | @step H M' K' hHM hn hMK ih =>
    have hn' : ∀ y ∈ M', ∀ n ∈ H, y * n * y⁻¹ ∈ H := fun y hy n hn0 => by
      have := hn.conj_mem ⟨n, hHM hn0⟩ (Subgroup.mem_subgroupOf.2 hn0) ⟨y, hy⟩
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have h1 := isSylowIn_inf_of_normal' (ih hQ) hHM hn'
    rwa [inf_assoc, inf_eq_right.2 hHM] at h1

theorem false_of_sylow_le_center {Y : Type} [Group Y] [Finite Y]
    (h : IsLThreeFour (Y ⧸ Subgroup.center Y)) (P : Sylow 3 Y)
    (hP : (P : Subgroup Y) ≤ Subgroup.center Y) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (Y ⧸ Subgroup.center Y) = 20160 :=
    CFSG.HardMathSupport.Solomon.Coordinator.card_of_isLThreeFour h
  have hdvd : (Subgroup.center Y).index ∣ (P : Subgroup Y).index := Subgroup.index_dvd_of_le hP
  have hidx : (Subgroup.center Y).index = 20160 := by rw [Subgroup.index, hcard]
  rw [hidx] at hdvd
  exact P.not_dvd_index (dvd_trans (by norm_num) hdvd)

theorem conj_eq_of_mem_zpowers {x n : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {k : ℕ}
    (hn : n ^ (3 ^ k) = 1) (h : n * x * n⁻¹ ∈ Subgroup.zpowers x) : n * x * n⁻¹ = x := by
  rcases mem_zpowers_of_pow_three hx3 h with h1 | h2 | h3
  · exfalso
    apply hx1
    have : x = n⁻¹ * (n * x * n⁻¹) * n := by group
    rw [this, h1]
    group
  · exact h2
  · exfalso
    have hsq : (n * n) * x * (n * n)⁻¹ = x := by
      have e : (n * n) * x * (n * n)⁻¹ = n * (n * x * n⁻¹) * n⁻¹ := by group
      rw [e, h3]
      have e2 : n * (x * x) * n⁻¹ = (n * x * n⁻¹) * (n * x * n⁻¹) := by group
      rw [e2, h3]
      calc x * x * (x * x) = x ^ 3 * x := by rw [pow_three]; group
        _ = x := by rw [hx3, one_mul]
    have hcomm : Commute (n * n) x := by
      show (n * n) * x = x * (n * n)
      calc (n * n) * x = ((n * n) * x * (n * n)⁻¹) * (n * n) := by group
        _ = x * (n * n) := by rw [hsq]
    obtain ⟨t, ht⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have hnm : (n * n) ^ (t + 1) = n := by
      have e1 : (n * n) ^ (t + 1) = n ^ (2 * (t + 1)) := by rw [← sq, ← pow_mul]
      have e2 : 2 * (t + 1) = 3 ^ k + 1 := by omega
      rw [e1, e2, pow_succ, hn, one_mul]
    have hnx : n * x * n⁻¹ = x := by
      have := (hcomm.pow_left (t + 1)).eq
      rw [hnm] at this
      rw [this]
      group
    rw [hnx] at h3
    apply hx1
    have : x * x = x * 1 := by rw [← h3, mul_one]
    exact mul_left_cancel this

theorem mem_normalizer_of_centralizes_sylow {X Q I : Subgroup G} (hI : GLAPComponent 3 X I)
    (hIt : IsLThreeFour (barOf 3 I ⧸ Subgroup.center (barOf 3 I))) (hQ : IsSylowIn 3 X Q)
    {z : G} (hzX : z ∈ X) (hz : ∀ q ∈ Q, q * z = z * q) : z ∈ Subgroup.normalizer (I : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  by_contra hzN
  have hXz : GLBConj z X = X := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hzX)
  have hI' : GLAPComponent 3 X (GLBConj z I) := by
    have := glaPComponent_gLBConj hI z
    rwa [hXz] at this
  have hne : GLBConj z I ≠ I := fun he => hzN (mem_normalizer_iff_gLBConj_eq.2 he)
  have hT : IsSylowIn 3 I (Q ⊓ I) := isSylowIn_inf_of_isSubnormal hQ hI.2.1
  have hTI' : Q ⊓ I ≤ GLBConj z I := by
    intro t ht
    rw [mem_gLBConj]
    have e : z * t * z⁻¹ = t := by
      rw [← hz t ht.1]
      group
    rw [e]
    exact ht.2
  obtain ⟨T₀, hT₀⟩ := exists_sylow_of_isSylowIn hT
  set Y := barX 3 X I with hY
  let f : ↥I →* ↥Y := ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (Subgroup.inclusion hI.1)).codRestrict
    Y (fun t => ⟨Subgroup.inclusion hI.1 t, Subgroup.mem_subgroupOf.2 t.2, rfl⟩)
  have hsurj : Function.Surjective f := by
    rintro ⟨_, ⟨⟨l, hlX⟩, hl, rfl⟩⟩
    exact ⟨⟨l, Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩
  set P : Sylow 3 ↥Y := T₀.mapSurjective hsurj with hP
  have hIt' : IsLThreeFour (↥Y ⧸ Subgroup.center ↥Y) :=
    Lemma1245.isLThreeFour_modCenter_congr (quotEquivBarX hp3 hI.1 hI.2.1) hIt
  refine false_of_sylow_le_center hIt' P ?_
  intro u hu
  rw [hP, Sylow.coe_mapSurjective, hT₀] at hu
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hu
  have htT : (t : G) ∈ Q ⊓ I := Subgroup.mem_subgroupOf.1 ht
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  have hmem : (f t : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ barX 3 X (GLBConj z I) :=
    ⟨⟨t, hI.1 t.2⟩, Subgroup.mem_subgroupOf.2 (hTI' htT), rfl⟩
  exact commute_of_glaPComponent_ne hI hI' (Ne.symm hne) w.2 hmem

theorem isElemAbelian_zpowers_of_pow_three {Y : Type} [Group Y] {w : Y} (hw : w ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers w) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    show (a : Y) * b = b * a
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self w i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]

end NormHelpers

section NormCases

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_of_normalizes {m : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m 3 B M E A a)
    {K : Subgroup G} (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    (hA4 : CFSG.Open.pRank 3 A = 4) {x : G} (hx : x ∈ centBar 3 A K) (hx1 : x ≠ 1)
    {I : Subgroup G} (hIX : I ≤ Cg x) (hIN : E ⊓ A ≤ Subgroup.normalizer (I : Set G))
    (hAI : ¬ A ≤ Subgroup.normalizer (I : Set G)) {z : G} (hzA : z ∈ A)
    (hzN : z ∈ Subgroup.normalizer (I : Set G)) : z ∈ (E ⊓ A) ⊔ Subgroup.zpowers x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hxA : x ∈ A := (inf_le_right : centBar 3 A K ≤ A) hx
  have hx3 : x ^ 3 = 1 := hAel.2 x hxA
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hcardA : Nat.card A = 3 ^ 4 := Lemma124.card_eq_of_pRank_four hAel hA4
  have hxI : x ∈ Subgroup.normalizer (I : Set G) := Lemma1112b.mem_normalizer_of_central fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (hIX hk) x (Set.mem_singleton x))
  have hdisj0 : (E ⊓ A) ⊓ centBar 3 A K = ⊥ := Lemma124.inter_disjoint_centBar_of_faithful hA0.2
  have hA0x : (E ⊓ A) ⊓ Subgroup.zpowers x = ⊥ :=
    le_bot_iff.1 (hdisj0 ▸ inf_le_inf_left _ (Subgroup.zpowers_le.2 hx))
  have hcomm : ∀ b ∈ E ⊓ A, ∀ u ∈ Subgroup.zpowers x, b * u = u * b := fun b hb u hu =>
    CFSG.Open.IsElemAbelian.comm hAel (Subgroup.mem_inf.1 hb).2 ((Subgroup.zpowers_le.2 hxA) hu)
  have hN0card : Nat.card ((E ⊓ A) ⊔ Subgroup.zpowers x : Subgroup G) = 27 := by
    rw [Lemma124.card_eq_mul_of_sup_eq hcomm rfl hA0x, hA0.1, Nat.card_zpowers, hxo]
  set N : Subgroup G := A ⊓ Subgroup.normalizer (I : Set G) with hN
  have hN0N : (E ⊓ A) ⊔ Subgroup.zpowers x ≤ N :=
    sup_le (le_inf inf_le_right hIN) (Subgroup.zpowers_le.2 ⟨hxA, hxI⟩)
  have hNA : N ≤ A := inf_le_left
  obtain ⟨i, hi, hNi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (hcardA ▸ Subgroup.card_dvd_of_le hNA : Nat.card N ∣ 3 ^ 4)
  have h27 : 27 ≤ Nat.card N := hN0card ▸ Subgroup.card_le_of_le hN0N
  have hi34 : i = 3 ∨ i = 4 := by
    rw [hNi] at h27
    have : 3 ≤ i := by
      by_contra hlt
      push Not at hlt
      have : 3 ^ i ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  rcases hi34 with rfl | rfl
  · have heq : (E ⊓ A) ⊔ Subgroup.zpowers x = N :=
      Subgroup.eq_of_le_of_card_ge hN0N (by rw [hNi, hN0card]; norm_num)
    rw [heq]
    exact ⟨hzA, hzN⟩
  · exfalso
    apply hAI
    have heq : N = A := Subgroup.eq_of_le_of_card_ge hNA (by rw [hNi, hcardA])
    rw [← heq]
    exact inf_le_right

theorem normF_false_of_center_ne_bot (h104i : Lemma104_iStatement) (h104ii : Lemma104_iiStatement)
    (h104iii : Lemma104_iiiStatement) (h104iv : Lemma104_ivStatement) (h104vi : Lemma104_viStatement)
    (h3110 : Input31_10L34) (hSL : InputSL34SylowCent)
    {m : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m 3 B M E A a) {K : Subgroup G}
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    (hA4 : CFSG.Open.pRank 3 A = 4) {x : G} (hx : x ∈ centBar 3 A K) (hx1 : x ≠ 1)
    {I : Subgroup G} (hI : GLAPComponent 3 (Cg x) I)
    (hIt : IsLThreeFour (barOf 3 I ⧸ Subgroup.center (barOf 3 I)))
    (hIN : E ⊓ A ≤ Subgroup.normalizer (I : Set G))
    (hIf : ∀ b ∈ E ⊓ A, b ∈ centBar 3 ⊤ I → b = 1)
    (hAI : ¬ A ≤ Subgroup.normalizer (I : Set G)) (hZ : Subgroup.center (barOf 3 I) ≠ ⊥) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hA3 : IsPGroup 3 ↥A := Lemma124.isPGroup_three_of_isElemAbelian hAel
  have hSC : IsSCp 3 ⊤ A := (h104ii h.toSec11.toSec10Fails h.pair).2
  have hA0el : IsElemAbelian 3 (E ⊓ A) := Lemma124.isElemAbelian_of_le inf_le_right hAel
  have hk : CFSG.Open.pRank 3 (E ⊓ A) = 2 := Lemma124.pRank_eq_two_of_card_nine hA0el hA0.1
  have hxA : x ∈ A := (inf_le_right : centBar 3 A K ≤ A) hx
  have hcommA : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc =>
    CFSG.Open.IsElemAbelian.comm hAel hb hc
  have hAX : A ≤ Cg x := fun b hb => Subgroup.mem_centralizer_iff.2 fun w hw => by
    rw [Set.mem_singleton_iff.1 hw]
    exact hcommA x hxA b hb
  have hx3 : x ^ 3 = 1 := hAel.2 x hxA
  have hq : CFSG.Open.IsQuasisimple (barOf 3 I) := l119_isQuasisimple_barOf (p := 3) (by norm_num) hI
  have hO : GLAPPrimeCore 3 (barOf 3 I) = ⊥ := glaPPrimeCore_quotient_eq_bot (p := 3) (by norm_num)
  have hxcI : ∀ u ∈ Subgroup.zpowers x, ∀ k ∈ I, u * k = k * u := by
    intro u hu k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    exact (Commute.zpow_left (Subgroup.mem_centralizer_iff.1 (hI.1 hk) x (Set.mem_singleton x)) j).eq
  obtain ⟨Q, hQ, hAQ⟩ := Lemma1112b.exists_isSylowIn_ge hAX hA3
  have hxQ : x ∈ Q := hAQ hxA
  have hxZQ : x ∈ centerOf Q := Lemma1112b.mem_centerOf_of_mem hxQ hQ.1
  have hT : IsSylowIn 3 I (Q ⊓ I) := isSylowIn_inf_of_isSubnormal hQ hI.2.1
  obtain ⟨T₀, hT₀⟩ := exists_sylow_of_isSylowIn hT
  set Pbar : Sylow 3 (barOf 3 I) :=
    T₀.mapSurjective (QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥I)) with hPbar
  have hZQ : ∀ z ∈ centerOf Q, z ^ 3 = 1 → z ∈ Subgroup.zpowers x := by
    intro z hzZ hz3
    by_cases hz1 : z = 1
    · rw [hz1]
      exact Subgroup.one_mem _
    have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have hzA : z ∈ A := Lemma1112b.le_of_centerOf_of_isSCp hAel hSC hAQ (Subgroup.zpowers_le.2 hzZ)
      (by rw [Nat.card_zpowers, hzo]) (Subgroup.mem_zpowers z)
    have hzcomm : ∀ q ∈ Q, q * z = z * q := comm_of_mem_centerOf hzZ
    have hzN : z ∈ Subgroup.normalizer (I : Set G) :=
      mem_normalizer_of_centralizes_sylow hI hIt hQ (hAX hzA) hzcomm
    have hfix : ∀ y ∈ (Pbar : Subgroup (barOf 3 I)), barAut 3 I ⟨z, hzN⟩ y = y := by
      intro y hy
      rw [hPbar, Sylow.coe_mapSurjective, hT₀] at hy
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hy
      rw [QuotientGroup.mk'_apply, CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
      congr 1
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hc := hzcomm t (Subgroup.mem_subgroupOf.1 ht).1
      calc z * (t : G) * z⁻¹ = ((t : G) * z) * z⁻¹ := by rw [hc]
        _ = t := by group
    have hpow : barAut 3 I ⟨z, hzN⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨z, hzN⟩ : ↥(Subgroup.normalizer (I : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
      rw [this, map_one]
    have hz1' : barAut 3 I ⟨z, hzN⟩ = 1 := hSL (barOf 3 I) hq hO hIt hZ _ hpow Pbar hfix
    obtain ⟨e, he, u, hu, rfl⟩ := Lemma124.exists_mul_of_mem_sup
      (fun b hb u hu => hcommA b (Subgroup.mem_inf.1 hb).2 u ((Subgroup.zpowers_le.2 hxA) hu))
      (mem_sup_of_normalizes h hA0 hA4 hx hx1 hI.1 hIN hAI hzA hzN)
    have heN : e ∈ Subgroup.normalizer (I : Set G) := hIN he
    have huN : u ∈ Subgroup.normalizer (I : Set G) :=
      Lemma1112b.mem_normalizer_of_central (hxcI u hu)
    have hu1 : barAut 3 I ⟨u, huN⟩ = 1 :=
      Lemma1112b.barAut_eq_one_of_central ⟨u, huN⟩ (hxcI u hu)
    have he1 : barAut 3 I ⟨e, heN⟩ = 1 := by
      have hmul : (⟨e * u, hzN⟩ : ↥(Subgroup.normalizer (I : Set G))) = ⟨e, heN⟩ * ⟨u, huN⟩ :=
        Subtype.ext rfl
      rw [hmul, map_mul, hu1, mul_one] at hz1'
      exact hz1'
    have hee : e = 1 := hIf e he ⟨Subgroup.mem_map.2 ⟨⟨e, heN⟩, MonoidHom.mem_ker.2 he1, rfl⟩,
      Subgroup.mem_top e⟩
    rw [hee, one_mul]
    exact hu
  have hQG : IsSylowIn 3 ⊤ Q := by
    refine ⟨le_top, hQ.2.1, fun Q' _ hQ'3 hQQ' => ?_⟩
    by_contra hne
    obtain ⟨n, hnQ', hnN, hnQ⟩ := Lemma1112b.exists_mem_normalizer_not_mem hQ'3 hQQ' (Ne.symm hne)
    have hnxZ : n * x * n⁻¹ ∈ centerOf Q := by
      rw [Lemma1211.mem_centerOf_iff']
      refine ⟨(Subgroup.mem_normalizer_iff.1 hnN x).1 hxQ, fun q hq => ?_⟩
      have hq' : n⁻¹ * q * n ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnN) q).1 hq
        simpa using this
      have hc := (comm_of_mem_centerOf hxZQ) _ hq'
      calc q * (n * x * n⁻¹) = n * ((n⁻¹ * q * n) * x) * n⁻¹ := by group
        _ = n * (x * (n⁻¹ * q * n)) * n⁻¹ := by rw [hc]
        _ = n * x * n⁻¹ * q := by group
    have hnx3 : (n * x * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
    obtain ⟨j, hj⟩ := hQ'3 ⟨n, hnQ'⟩
    have hnj : n ^ (3 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    have hnxe : n * x * n⁻¹ = x := conj_eq_of_mem_zpowers hx3 hx1 hnj (hZQ _ hnxZ hnx3)
    have hnC : n ∈ Cg x := Subgroup.mem_centralizer_iff.2 fun w hw => by
      rw [Set.mem_singleton_iff.1 hw]
      calc x * n = (n * x * n⁻¹) * n := by rw [hnxe]
        _ = n * x := by group
    have hle : Q ⊔ Subgroup.zpowers n ≤ Cg x := sup_le hQ.1 (Subgroup.zpowers_le.2 hnC)
    have hp : IsPGroup 3 ↥(Q ⊔ Subgroup.zpowers n) :=
      hQ'3.to_le (sup_le hQQ' (Subgroup.zpowers_le.2 hnQ'))
    have heq := hQ.2.2 _ hle hp le_sup_left
    exact hnQ (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
  have hconnQ := h3110 (Cg x) I hI hIt Q hQ
  exact false_of_sylow_connected h104i h104ii h104iii h104iv h104vi h hk hA4 hQG
    (fun U V hU hV => isKConnectedIn_top_of (hconnQ U V hU hV))

theorem normF_false_of_center_bot (h104ii : Lemma104_iiStatement) (h104iii : Lemma104_iiiStatement)
    (h104iv : Lemma104_ivStatement) (h111 : Prop111Statement)
    {m : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m 3 B M E A a) {K : Subgroup G}
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K)
    {x : G} (hx : x ∈ centBar 3 A K) (hx1 : x ≠ 1)
    {I : Subgroup G} (hI : GLAPComponent 3 (Cg x) I)
    (hIt : IsLThreeFour (barOf 3 I ⧸ Subgroup.center (barOf 3 I)))
    (hIN : E ⊓ A ≤ Subgroup.normalizer (I : Set G)) (hIinn : ∀ b ∈ E ⊓ A, InducesInner 3 I b)
    (hIf : ∀ b ∈ E ⊓ A, b ∈ centBar 3 ⊤ I → b = 1)
    (hAI : ¬ A ≤ Subgroup.normalizer (I : Set G)) (hIM : ¬ I ≤ M)
    (hZ : Subgroup.center (barOf 3 I) = ⊥) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hA0A : E ⊓ A ≤ A := inf_le_right
  have hA0el : IsElemAbelian 3 (E ⊓ A) := Lemma124.isElemAbelian_of_le hA0A hAel
  have hk : CFSG.Open.pRank 3 (E ⊓ A) = 2 := Lemma124.pRank_eq_two_of_card_nine hA0el hA0.1
  have hxA : x ∈ A := (inf_le_right : centBar 3 A K ≤ A) hx
  have hcommA : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc =>
    CFSG.Open.IsElemAbelian.comm hAel hb hc
  set X := Cg x with hXdef
  have hAX : A ≤ X := fun b hb => Subgroup.mem_centralizer_iff.2 fun w hw => by
    rw [Set.mem_singleton_iff.1 hw]
    exact hcommA x hxA b hb
  have hxX : x ∈ X := hAX hxA
  have hx3 : x ^ 3 = 1 := hAel.2 x hxA
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨y, hyA, hyI⟩ : ∃ y ∈ A, y ∉ Subgroup.normalizer (I : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hAI hcon
  have hyX : y ∈ X := hAX hyA
  set φ : ↥(E ⊓ A) →* MulAut (barOf 3 I) := (barAut 3 I).comp (Subgroup.inclusion hIN) with hφ
  have hconj_inj : Function.Injective (MulAut.conj : barOf 3 I →* MulAut (barOf 3 I)) :=
    Lemma1245.conj_injective_of_center_bot hZ
  set Pbar : Subgroup (barOf 3 I) := φ.range.comap MulAut.conj with hPbar
  have hinn : ∀ b (hb : b ∈ E ⊓ A), ∃ c : barOf 3 I, barAut 3 I ⟨b, hIN hb⟩ = MulAut.conj c :=
    fun b hb => Lemma1245.exists_conj_of_inducesInner (hIN hb) (hIinn b hb)
  have hmap : Pbar.map MulAut.conj = φ.range := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz
    · rintro _ ⟨⟨b, hb⟩, rfl⟩
      obtain ⟨c, hc⟩ := hinn b hb
      have hcc : MulAut.conj c = φ ⟨b, hb⟩ := hc.symm
      exact ⟨c, ⟨⟨b, hb⟩, hcc.symm⟩, hcc⟩
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨b, hb⟩ h1
    have hb1 : b ∈ centBar 3 ⊤ I :=
      ⟨Subgroup.mem_map.2 ⟨⟨b, hIN hb⟩, MonoidHom.mem_ker.2 h1, rfl⟩, Subgroup.mem_top b⟩
    exact Subtype.ext (hIf b hb hb1)
  have hPcard : Nat.card Pbar = 9 := by
    have h1 := Subgroup.card_map_of_injective (K := Pbar) hconj_inj
    rw [hmap] at h1
    rw [← h1, ← hA0.1]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have hφcomm : ∀ u v : ↥(E ⊓ A), φ u * φ v = φ v * φ u := fun u v => by
    rw [← map_mul, ← map_mul, hA0el.1.is_comm.comm u v]
  have hPcomm : ∀ z ∈ Pbar, ∀ w ∈ Pbar, z * w = w * z := by
    intro z hz w hw
    obtain ⟨u, hu⟩ := hz
    obtain ⟨v, hv⟩ := hw
    apply hconj_inj
    rw [map_mul, map_mul]
    show MulAut.conj z * MulAut.conj w = MulAut.conj w * MulAut.conj z
    rw [← hu, ← hv]
    exact hφcomm u v
  have hPexp : ∀ z ∈ Pbar, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨u, hu⟩ := hz
    apply hconj_inj
    rw [map_pow, map_one]
    show (MulAut.conj z) ^ 3 = 1
    rw [← hu, ← map_pow]
    have : u ^ 3 = 1 := Subtype.ext (by simpa using hA0el.2 u.1 u.2)
    rw [this, map_one]
  have hPfix : ∀ b (hb : b ∈ E ⊓ A), ∀ z ∈ Pbar, barAut 3 I ⟨b, hIN hb⟩ z = z := by
    intro b hb z hz
    obtain ⟨c, hc⟩ := hinn b hb
    have hcP : c ∈ Pbar := ⟨⟨b, hb⟩, hc⟩
    rw [hc, MulAut.conj_apply, hPcomm c hcP z hz]
    group
  have hPbarel : IsElemAbelian 3 Pbar :=
    ⟨⟨⟨fun u v => Subtype.ext (hPcomm u u.2 v v.2)⟩⟩, hPexp⟩
  set π : ↥X →* ↥X ⧸ GLAPPrimeCore 3 ↥X := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hπ
  set e := quotEquivBarX hp3 hI.1 hI.2.1 with he
  set P1 : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) :=
    (Pbar.map e.toMonoidHom).map (barX 3 X I).subtype with hP1
  have hP1I : P1 ≤ barX 3 X I := Subgroup.map_subtype_le _
  have hP1mem : ∀ u ∈ P1, ∃ z ∈ Pbar, u = ((e z : ↥(barX 3 X I)) : ↥X ⧸ GLAPPrimeCore 3 ↥X) := by
    intro u hu
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hu'
    exact ⟨z, hz, rfl⟩
  have hP1card : Nat.card P1 = 9 := by
    rw [hP1, Subgroup.card_map_of_injective (barX 3 X I).subtype_injective,
      Subgroup.card_map_of_injective e.injective, hPcard]
  have hP1el : IsElemAbelian 3 P1 :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hPbarel _) _
  have hP1fix : ∀ b (hb : b ∈ E ⊓ A), ∀ u ∈ P1,
      π ⟨b, hAX (hA0A hb)⟩ * u = u * π ⟨b, hAX (hA0A hb)⟩ := by
    intro b hb u hu
    obtain ⟨z, hz, rfl⟩ := hP1mem u hu
    have h1 := Lemma129b.quotEquivBarX_barAut hp3 hI (hAX (hA0A hb)) (hIN hb) z
    rw [hPfix b hb z hz] at h1
    calc π ⟨b, hAX (hA0A hb)⟩ * ((e z : ↥(barX 3 X I)) : ↥X ⧸ GLAPPrimeCore 3 ↥X)
        = (π ⟨b, hAX (hA0A hb)⟩ * ((e z : ↥(barX 3 X I)) : ↥X ⧸ GLAPPrimeCore 3 ↥X) *
            (π ⟨b, hAX (hA0A hb)⟩)⁻¹) * π ⟨b, hAX (hA0A hb)⟩ := by group
      _ = ((e z : ↥(barX 3 X I)) : ↥X ⧸ GLAPPrimeCore 3 ↥X) * π ⟨b, hAX (hA0A hb)⟩ := by
        rw [← h1]
  set yb := π ⟨y, hyX⟩ with hyb
  set P2 : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) := P1.map (MulAut.conj yb⁻¹).toMonoidHom with hP2
  have hP2mem : ∀ u ∈ P2, ∃ v ∈ P1, u = yb⁻¹ * v * yb := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hu
    exact ⟨v, hv, by simp [MulAut.conj_apply]⟩
  have hP2card : Nat.card P2 = 9 := by
    rw [hP2, Subgroup.card_map_of_injective (MulAut.conj yb⁻¹).injective, hP1card]
  have hP2el : IsElemAbelian 3 P2 := CFSG.SectionRank.isElemAbelian_map hP1el _
  have hXy : GLBConj y X = X := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hyX)
  have hI2 : GLAPComponent 3 X (GLBConj y I) := by
    have := glaPComponent_gLBConj hI y
    rwa [hXy] at this
  have hGy : GLBConj y I ≠ I := fun he' => hyI (mem_normalizer_iff_gLBConj_eq.2 he')
  have hP2I : P2 ≤ barX 3 X (GLBConj y I) := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hP2mem u hu
    rw [mem_barX_gLBConj hI.1 hyX]
    have e1 : π ⟨y, hyX⟩ * (yb⁻¹ * v * yb) * (π ⟨y, hyX⟩)⁻¹ = v := by
      rw [← hyb]
      group
    rw [e1]
    exact hP1I hv
  have hP2fix : ∀ b (hb : b ∈ E ⊓ A), ∀ u ∈ P2,
      π ⟨b, hAX (hA0A hb)⟩ * u = u * π ⟨b, hAX (hA0A hb)⟩ := by
    intro b hb u hu
    obtain ⟨v, hv, rfl⟩ := hP2mem u hu
    set bb := π ⟨b, hAX (hA0A hb)⟩ with hbb
    have hby : bb * yb = yb * bb := by
      rw [hbb, hyb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcommA b (hA0A hb) y hyA)
    have hby' : bb * yb⁻¹ = yb⁻¹ * bb := by
      calc bb * yb⁻¹ = yb⁻¹ * (yb * bb) * yb⁻¹ := by group
        _ = yb⁻¹ * (bb * yb) * yb⁻¹ := by rw [hby]
        _ = yb⁻¹ * bb := by group
    have hbv := hP1fix b hb v hv
    calc bb * (yb⁻¹ * v * yb) = (bb * yb⁻¹) * v * yb := by group
      _ = (yb⁻¹ * bb) * v * yb := by rw [hby']
      _ = yb⁻¹ * (bb * v) * yb := by group
      _ = yb⁻¹ * (v * bb) * yb := by rw [hbv]
      _ = yb⁻¹ * v * (bb * yb) := by group
      _ = yb⁻¹ * v * (yb * bb) := by rw [hby]
      _ = (yb⁻¹ * v * yb) * bb := by group
  set xb := π ⟨x, hxX⟩ with hxb
  have hxbcen : ∀ w : ↥X ⧸ GLAPPrimeCore 3 ↥X, xb * w = w * xb := by
    intro w
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ w
    rw [hxb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 c.2 x (Set.mem_singleton x))
  have hxb3 : xb ^ 3 = 1 := by
    rw [hxb, ← map_pow]
    have : (⟨x, hxX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hxbo : orderOf xb = 3 := by
    refine orderOf_eq_prime hxb3 fun hxb1 => ?_
    have hxO : x ∈ GLAPPrimeCoreOf 3 X := (mem_glaPPrimeCoreOf_iff hxX).2 hxb1
    exact Prop115.orderOf_ne_of_coprime_card hp3 hxO (sec11_glaPPrimeCoreOf_coprime X) hxo
  have hIc' : Subgroup.center ↥(barX 3 X I) = ⊥ := center_barX_eq_bot hI hZ
  have hc12 : ∀ u ∈ P1, ∀ v ∈ P2, u * v = v * u := fun u hu v hv =>
    commute_of_glaPComponent_ne hI hI2 (Ne.symm hGy) (hP1I hu) (hP2I hv)
  have hP12el : IsElemAbelian 3 (P1 ⊔ P2) := isElemAbelian_sup_of_commute hP1el hP2el
    (fun u hu => Subgroup.mem_centralizer_iff.2 fun v hv => (hc12 u hu v hv).symm)
  have hDel : IsElemAbelian 3 ((P1 ⊔ P2) ⊔ Subgroup.zpowers xb) :=
    isElemAbelian_sup_of_commute hP12el (isElemAbelian_zpowers_of_pow_three hxb3)
      (fun u _ => Subgroup.mem_centralizer_iff.2 fun v hv => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
        exact (Commute.zpow_left (hxbcen u) i).eq)
  have hP12disj : P1 ⊓ P2 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have hmem : (⟨u, hP1I hu.1⟩ : ↥(barX 3 X I)) ∈ Subgroup.center ↥(barX 3 X I) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact commute_of_glaPComponent_ne hI hI2 (Ne.symm hGy) w.2 (hP2I hu.2)
    rw [hIc', Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hP12card : Nat.card (P1 ⊔ P2 : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) = 81 := by
    rw [Lemma124.card_eq_mul_of_sup_eq hc12 rfl hP12disj, hP1card, hP2card]
  have hP12x : (P1 ⊔ P2) ⊓ Subgroup.zpowers xb = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    obtain ⟨u, hu, v, hv, rfl⟩ := Lemma124.exists_mul_of_mem_sup hc12 hw.1
    have hwc : ∀ t, (u * v) * t = t * (u * v) := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hw.2
      intro t
      rw [← hi]
      exact (Commute.zpow_left (hxbcen t) i).eq
    have hu1 : u = 1 := by
      have hmem : (⟨u, hP1I hu⟩ : ↥(barX 3 X I)) ∈ Subgroup.center ↥(barX 3 X I) := by
        rw [Subgroup.mem_center_iff]
        intro t
        apply Subtype.ext
        have h1 := hwc t
        have h2 : (t : ↥X ⧸ GLAPPrimeCore 3 ↥X) * v = v * t :=
          commute_of_glaPComponent_ne hI hI2 (Ne.symm hGy) t.2 (hP2I hv)
        show (t : ↥X ⧸ GLAPPrimeCore 3 ↥X) * u = u * t
        calc (t : ↥X ⧸ GLAPPrimeCore 3 ↥X) * u = t * ((u * v) * v⁻¹) := by group
          _ = (t * (u * v)) * v⁻¹ := by group
          _ = ((u * v) * t) * v⁻¹ := by rw [h1]
          _ = u * (v * t) * v⁻¹ := by group
          _ = u * (t * v) * v⁻¹ := by rw [h2]
          _ = u * t := by group
      rw [hIc', Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    subst hu1
    rw [one_mul] at hwc ⊢
    have hv' : yb * v * yb⁻¹ ∈ barX 3 X I := (mem_barX_gLBConj hI.1 hyX v).1 (hP2I hv)
    have hvc : yb * v * yb⁻¹ = v := by
      rw [← hwc yb]
      group
    rw [hvc] at hv'
    have hmem : (⟨v, hv'⟩ : ↥(barX 3 X I)) ∈ Subgroup.center ↥(barX 3 X I) := by
      rw [Subgroup.mem_center_iff]
      intro t
      apply Subtype.ext
      exact (hwc t).symm
    rw [hIc', Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  set Dt := (P1 ⊔ P2) ⊔ Subgroup.zpowers xb with hDt
  have hDcard : Nat.card Dt = 3 ^ 5 := by
    rw [hDt, Lemma124.card_eq_mul_of_sup_eq (fun u _ v hv => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
        exact (Commute.zpow_left (hxbcen u) i).eq.symm) rfl hP12x,
      hP12card, Nat.card_zpowers, hxbo]
    norm_num
  have hDfix : ∀ b (hb : b ∈ E ⊓ A), ∀ w ∈ Dt,
      π ⟨b, hAX (hA0A hb)⟩ * w = w * π ⟨b, hAX (hA0A hb)⟩ := by
    intro b hb w hw
    have hle : Dt ≤ Subgroup.centralizer ({π ⟨b, hAX (hA0A hb)⟩} : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        rw [Set.mem_singleton_iff.1 ht]
        exact hP1fix b hb u hu
      · intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        rw [Set.mem_singleton_iff.1 ht]
        exact hP2fix b hb u hu
      · intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        rw [Set.mem_singleton_iff.1 ht]
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
        exact (Commute.zpow_left (hxbcen _) i).eq.symm
    exact Subgroup.mem_centralizer_iff.1 (hle hw) _ (Set.mem_singleton _)
  set H : Subgroup G := (Dt.comap π).map X.subtype with hH
  have hHX : H ≤ X := Subgroup.map_subtype_le _
  have hmemH : ∀ c : ↥X, (c : G) ∈ H ↔ π c ∈ Dt := by
    intro c
    constructor
    · rintro ⟨d, hd, hdc⟩
      have hdc' : d = c := Subtype.ext hdc
      rw [← hdc']
      exact hd
    · intro hc
      exact ⟨c, hc, rfl⟩
  have hA0X : E ⊓ A ≤ X := hA0A.trans hAX
  have hconjH : ∀ b (hb : b ∈ E ⊓ A) (c : ↥X), π c ∈ Dt →
      π ⟨b * (c : G) * b⁻¹, X.mul_mem (X.mul_mem (hA0X hb) c.2) (X.inv_mem (hA0X hb))⟩ = π c := by
    intro b hb c hc
    have e1 : (⟨b * (c : G) * b⁻¹, X.mul_mem (X.mul_mem (hA0X hb) c.2) (X.inv_mem (hA0X hb))⟩ : ↥X) =
        ⟨b, hA0X hb⟩ * c * ⟨b, hA0X hb⟩⁻¹ := Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv, hDfix b hb (π c) hc, mul_inv_cancel_right]
  have hA0N : E ⊓ A ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb c hc
    obtain ⟨d, hd, rfl⟩ := hc
    refine (hmemH ⟨_, X.mul_mem (X.mul_mem (hA0X hb) d.2) (X.inv_mem (hA0X hb))⟩).2 ?_
    rw [hconjH b hb d hd]
    exact hd
  have hA03 : IsPGroup 3 ↥(E ⊓ A) := Lemma124.isPGroup_three_of_isElemAbelian hA0el
  have hker : ¬ 3 ∣ Nat.card ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp
      (Subgroup.inclusion hHX)).ker :=
    (Nat.Prime.coprime_iff_not_dvd hp3).1 (Lemma1245.ker_coprime_aux hHX)
  have htriv : ∀ (member : ↥(E ⊓ A)) (element : ↥H),
      ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (Subgroup.inclusion hHX))
        ⟨member * element * (member : G)⁻¹,
          Subgroup.le_normalizer_iff.mp hA0N member member.property element element.property⟩ =
      ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (Subgroup.inclusion hHX)) element := by
    rintro ⟨b, hb⟩ ⟨c, hc⟩
    have hcX : c ∈ X := hHX hc
    exact hconjH b hb ⟨c, hcX⟩ ((hmemH ⟨c, hcX⟩).1 hc)
  set C : Subgroup G := H ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) with hC
  have hCX : C ≤ X := inf_le_left.trans hHX
  have hbarC : barX 3 X C = Dt := by
    apply le_antisymm
    · rintro w ⟨c, hc, rfl⟩
      exact (hmemH c).1 (Subgroup.mem_subgroupOf.1 hc).1
    · intro w hw
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ w
      have hcH : (c : G) ∈ H := (hmemH c).2 hw
      obtain ⟨f, hfC, hf⟩ :=
        CFSG.RankThreeEvenClassification.Helpers.exists_centralizer_with_same_image_of_trivial_quotient_action
          3 hp3 (E ⊓ A) H hA03 hA0N _ hker htriv ⟨c, hcH⟩
      exact ⟨⟨f, hHX f.2⟩, Subgroup.mem_subgroupOf.2 ⟨f.2, hfC⟩, hf⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥C) := inferInstance
  set V : Subgroup G := (S : Subgroup ↥C).map C.subtype with hV
  have hVC : V ≤ C := Subgroup.map_subtype_le _
  have hVX : V ≤ X := hVC.trans hCX
  have hV3 : IsPGroup 3 ↥V := S.isPGroup'.map C.subtype
  have hDt3 : IsPGroup 3 ↥Dt := Lemma124.isPGroup_three_of_isElemAbelian hDel
  have hbarV : barX 3 X V = Dt := (barX_sylow_eq hCX (by rw [hbarC]; exact hDt3) S).trans hbarC
  have hVcard : Nat.card V = 3 ^ 5 := by rw [← card_barX_of_le hp3 hVX hV3, hbarV, hDcard]
  have hinjV := injective_barX_comp hp3 hV3 hVX
  have hπV : ∀ v (hv : v ∈ V), π ⟨v, hVX hv⟩ ∈ Dt := fun v hv =>
    hbarV ▸ ⟨⟨v, hVX hv⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩
  have hinj' : ∀ v w (hv : v ∈ V) (hw : w ∈ V), π ⟨v, hVX hv⟩ = π ⟨w, hVX hw⟩ → v = w := by
    intro v w hv hw hvw
    have h2 := hinjV (a₁ := ⟨⟨v, hVX hv⟩, hv⟩) (a₂ := ⟨⟨w, hVX hw⟩, hw⟩) hvw
    exact congrArg (fun z => ((z : ↥X) : G)) (congrArg Subtype.val h2)
  have hVel : IsElemAbelian 3 V := by
    refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun v hv => ?_⟩
    · apply hinj' _ _ (V.mul_mem u.2 v.2) (V.mul_mem v.2 u.2)
      have e1 : (⟨(u : G) * v, hVX (V.mul_mem u.2 v.2)⟩ : ↥X) = ⟨u, hVX u.2⟩ * ⟨v, hVX v.2⟩ := rfl
      have e2 : (⟨(v : G) * u, hVX (V.mul_mem v.2 u.2)⟩ : ↥X) = ⟨v, hVX v.2⟩ * ⟨u, hVX u.2⟩ := rfl
      rw [e1, e2, map_mul, map_mul]
      exact CFSG.Open.IsElemAbelian.comm hDel (hπV u u.2) (hπV v v.2)
    · apply hinj' _ _ (V.pow_mem hv 3) V.one_mem
      have e1 : (⟨v ^ 3, hVX (V.pow_mem hv 3)⟩ : ↥X) = ⟨v, hVX hv⟩ ^ 3 := Subtype.ext (by simp)
      rw [e1, map_pow, hDel.2 _ (hπV v hv)]
      exact (map_one π).symm
  have hVA0 : V ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) := hVC.trans inf_le_right
  exact hIM (le_M_of_rank_five h104ii h104iii h104iv h111 h hk hxA hx1 hI hIt hVel
    (by rw [hVcard]) hVX hVA0)

theorem normClaim_of_inputs (h104i : Lemma104_iStatement) (h104ii : Lemma104_iiStatement)
    (h104iii : Lemma104_iiiStatement) (h104iv : Lemma104_ivStatement) (h104vi : Lemma104_viStatement)
    (h111 : Prop111Statement) (h3110 : Input31_10L34) (hSL : InputSL34SylowCent) :
    Lemma1245.NormClaim := by
  intro G _ _ m B M E A a h K hK hK3 hKM hA0 hA4 x hx hx1 I hI hIt hIN hIinn hIf
  by_contra hcon
  push Not at hcon
  obtain ⟨hAI, hIM⟩ := hcon
  by_cases hZ : Subgroup.center (barOf 3 I) = ⊥
  · exact normF_false_of_center_bot h104ii h104iii h104iv h111 h hA0 hx hx1 hI hIt hIN hIinn hIf
      hAI hIM hZ
  · exact normF_false_of_center_ne_bot h104i h104ii h104iii h104iv h104vi h3110 hSL h hA0 hA4 hx hx1
      hI hIt hIN hIf hAI hZ

end NormCases

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1245

end
