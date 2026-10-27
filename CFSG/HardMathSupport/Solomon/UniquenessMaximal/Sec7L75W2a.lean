module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75X3a
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75X2
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L76A
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L76D

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

private theorem not_dvd_card_glaPPrimeCore_three (H : Type) [Group H] [Finite H] :
    ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card

theorem isLThreeFour_barX_quot {N K : Subgroup G} (hKN : K ≤ N)
    (h : IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K)) :
    IsLThreeFour (↥(barX 3 N K) ⧸ GLAPPrimeCore 3 ↥(barX 3 N K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := barX 3 N K with hP
  set Φ := barMap 3 hKN with hΦ
  have hΦs : Function.Surjective Φ := barMap_surjective hKN
  set g : ↥K →* (↥P ⧸ GLAPPrimeCore 3 ↥P) := (QuotientGroup.mk' _).comp Φ with hg
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hΦs
  have hOK : GLAPPrimeCore 3 ↥K ≤ g.ker := by
    have hnorm : ((GLAPPrimeCore 3 ↥K).map Φ).Normal :=
      (GLAPPrimeCore.normal 3 _).map Φ hΦs
    have hcop : Nat.Coprime 3 (Nat.card ((GLAPPrimeCore 3 ↥K).map Φ)) := by
      refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) ?_
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
        (not_dvd_card_glaPPrimeCore_three _)
    have hle : (GLAPPrimeCore 3 ↥K).map Φ ≤ GLAPPrimeCore 3 ↥P := le_sSup ⟨hnorm, hcop⟩
    intro k hk
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 (hle ⟨k, hk, rfl⟩)
  let f : (↥K ⧸ GLAPPrimeCore 3 ↥K) →* (↥P ⧸ GLAPPrimeCore 3 ↥P) :=
    QuotientGroup.lift _ g hOK
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨k, rfl⟩ := hgs z
    exact ⟨QuotientGroup.mk k, rfl⟩
  obtain ⟨hsimple, -⟩ := isSimpleGroup_of_isLThreeFour h
  rcases hsimple.eq_bot_or_eq_top_of_normal f.ker with hbot | htop
  · have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hbot
    exact IsLThreeFour.of_mulEquiv (MulEquiv.ofBijective f ⟨hinj, hfs⟩) h
  · exfalso
    have hPO : GLAPPrimeCore 3 ↥P = ⊤ := by
      refine eq_top_iff.2 fun p _ => ?_
      obtain ⟨k, rfl⟩ := hΦs p
      have h1 : (QuotientGroup.mk k : ↥K ⧸ GLAPPrimeCore 3 ↥K) ∈ f.ker := htop ▸ Subgroup.mem_top _
      have h2 : g k = 1 := h1
      exact (QuotientGroup.eq_one_iff _).1 h2
    have h3P : ¬ 3 ∣ Nat.card P := by
      have := not_dvd_card_glaPPrimeCore_three ↥P
      rwa [hPO, Subgroup.card_top] at this
    have h3K : 3 ∣ Nat.card K := by
      have h20160 : Nat.card (↥K ⧸ GLAPPrimeCore 3 ↥K) = 20160 := card_eq_of_isLThreeFour h
      have := Subgroup.card_quotient_dvd_card (GLAPPrimeCore 3 ↥K)
      rw [h20160] at this
      exact (by norm_num : 3 ∣ 20160).trans this
    have hker : ¬ 3 ∣ Nat.card Φ.ker := by
      let e : ↥Φ.ker →* ↥(GLAPPrimeCore 3 ↥N) :=
        ((Subgroup.inclusion hKN).comp Φ.ker.subtype).codRestrict _ (fun k => by
          have h1 : Φ k.1 = 1 := k.2
          have h2 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) (Subgroup.inclusion hKN k.1) = 1 :=
            congrArg Subtype.val h1
          exact (QuotientGroup.eq_one_iff _).1 h2)
      have he : Function.Injective e := by
        intro a b hab
        have h1 : Subgroup.inclusion hKN a.1 = Subgroup.inclusion hKN b.1 :=
          congrArg Subtype.val hab
        exact Subtype.ext (Subgroup.inclusion_injective hKN h1)
      intro hd
      exact not_dvd_card_glaPPrimeCore_three _ (hd.trans (Subgroup.card_dvd_of_injective e he))
    have hcard := Subgroup.card_ker_mul_card_range Φ
    rw [MonoidHom.range_eq_top.2 hΦs, Subgroup.card_top] at hcard
    rw [← hcard] at h3K
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3K with h4 | h4
    · exact hker h4
    · exact h3P h4

omit [Finite G] in
private theorem mem_glaPPrimeCoreOf_iff' {p : ℕ} {H : Subgroup G} (y : H) :
    (y : G) ∈ GLAPPrimeCoreOf p H ↔ y ∈ GLAPPrimeCore p ↥H := by
  constructor
  · rintro ⟨y', hy', e⟩
    have : y' = y := Subtype.ext e
    subst this
    exact hy'
  · intro h
    exact ⟨y, h, rfl⟩

private noncomputable def quotInfEquiv' {K N : Subgroup G} (hcov : Covers3 N K) :
    (↥(K ⊓ N) ⧸ GLAPPrimeCore 3 ↥(K ⊓ N)) ≃* (↥K ⧸ GLAPPrimeCore 3 ↥K) := by
  set H := K ⊓ N with hH
  set O := GLAPPrimeCoreOf 3 K with hO
  have hHK : H ≤ K := inf_le_left
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 K
  have hcov' : K ≤ H ⊔ O := by rwa [hH, inf_comm]
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := hHK.trans hKO
  let f : ↥H →* (↥K ⧸ GLAPPrimeCore 3 ↥K) :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hHK)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    have hk' : (k : G) ∈ ((H ⊔ O : Subgroup G) : Set G) := hcov' k.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H O hHO] at hk'
    obtain ⟨j, hj, o, ho, hjo⟩ := hk'
    refine ⟨⟨j, hj⟩, ?_⟩
    change QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (Subgroup.inclusion hHK ⟨j, hj⟩) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) k
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hmem : ((Subgroup.inclusion hHK ⟨j, hj⟩)⁻¹ * k : ↥K) ∈ GLAPPrimeCore 3 ↥K := by
      rw [← mem_glaPPrimeCoreOf_iff']
      have : (((Subgroup.inclusion hHK ⟨j, hj⟩)⁻¹ * k : ↥K) : G) = o := by
        have h1 : j * o = (k : G) := hjo
        simp [← h1]
      rw [this]
      exact ho
    exact hmem
  have hker : f.ker = GLAPPrimeCore 3 ↥H := by
    ext y
    rw [MonoidHom.mem_ker, ← mem_glaPPrimeCoreOf_iff', Sec7.glaPPrimeCoreOf_inf_eq hcov]
    change QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (Subgroup.inclusion hHK y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← mem_glaPPrimeCoreOf_iff']
    constructor
    · intro h
      exact ⟨y.2, h⟩
    · intro h
      exact h.2
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)


namespace Ctx75

variable {B N K : Subgroup G} {x : G}

theorem L34_inf (c : Ctx75 B N K x) :
    IsLThreeFour (↥(K ⊓ N) ⧸ GLAPPrimeCore 3 ↥(K ⊓ N)) :=
  IsLThreeFour.of_mulEquiv (quotInfEquiv' c.cov).symm c.hf.lThreeFour

theorem K0_le_N (c : Ctx75 B N K x) : GLAPLayer 3 (K ⊓ N) ≤ N :=
  c.layer_data.1.1.trans inf_le_right

theorem K0b_ne_bot (c : Ctx75 B N K x) : barX 3 N (GLAPLayer 3 (K ⊓ N)) ≠ ⊥ := by
  intro hbot
  set K0 := GLAPLayer 3 (K ⊓ N) with hK0
  have hK0Y : K0 ≤ K ⊓ N := c.layer_data.1.1
  have h1 : K0 ≤ GLAPPrimeCoreOf 3 N := Sec7.le_glaPPrimeCoreOf_of_barX_eq_bot c.K0_le_N hbot
  have h2 : ¬ 3 ∣ Nat.card K0 :=
    fun hd => not_dvd_card_glaPPrimeCoreOf Nat.prime_three N
      (hd.trans (Subgroup.card_dvd_of_le h1))
  have h3 : K0 ≤ GLAPPrimeCoreOf 3 (K ⊓ N) :=
    Lemma85Aux.le_glaPPrimeCoreOf_of_normalizes Nat.prime_three hK0Y
      (Sec7.le_normalizer_glaPLayer 3 (K ⊓ N)) h2
  have h4 : K0 ≤ GLAPPrimeCoreOf 3 K := by
    rw [Sec7.glaPPrimeCoreOf_inf_eq c.cov] at h3
    exact h3.trans inf_le_right
  have h5 : K ≤ GLAPPrimeCoreOf 3 K := c.layer_data.2.2.trans (sup_le h4 le_rfl)
  have h6 : ¬ 3 ∣ Nat.card K :=
    fun hd => not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
      (hd.trans (Subgroup.card_dvd_of_le h5))
  have h20160 : Nat.card (↥K ⧸ GLAPPrimeCore 3 ↥K) = 20160 :=
    card_eq_of_isLThreeFour c.hf.lThreeFour
  exact h6 ((by norm_num : 3 ∣ 20160).trans
    (h20160 ▸ Subgroup.card_quotient_dvd_card (GLAPPrimeCore 3 ↥K)))

theorem K0b_perf (c : Ctx75 B N K x) :
    ⁅barX 3 N (GLAPLayer 3 (K ⊓ N)), barX 3 N (GLAPLayer 3 (K ⊓ N))⁆ =
      barX 3 N (GLAPLayer 3 (K ⊓ N)) := by
  rw [← barX_commutator 3 c.K0_le_N c.K0_le_N, glaPComponent_perfect c.layer_data.1]

theorem K0b_gen (c : Ctx75 B N K x) :
    barX 3 N (GLAPLayer 3 (K ⊓ N)) = Subgroup.closure {g | g ∈ barX 3 N (GLAPLayer 3 (K ⊓ N)) ∧
      IsPGroup 3 (Subgroup.zpowers g)} := by
  set Y := K ⊓ N with hY
  set K0 := GLAPLayer 3 Y with hK0
  have hK0Y : K0 ≤ Y := c.layer_data.1.1
  have hsnK0 : IsSubnormal K0 Y := c.layer_data.1.2.1
  have hK0N : K0 ≤ N := c.K0_le_N
  set S : Set G := {g : G | g ∈ K0 ∧ IsPGroup 3 (Subgroup.zpowers g)} with hS
  set Z : Subgroup G := Subgroup.closure S with hZ
  have hZK0 : Z ≤ K0 := (Subgroup.closure_le K0).2 fun g hg => hg.1
  have hZeq : Z = K0 := by
    have hZn : K0 ≤ Subgroup.normalizer (Z : Set G) :=
      le_normalizer_closure_three (Subgroup.le_normalizer (H := K0))
    have hnZ : (Z.subgroupOf K0).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZK0).2 hZn
    have hsnZ : IsSubnormal Z Y :=
      isSubnormal_trans' (IsSubnormal.step hZK0 hnZ (IsSubnormal.refl K0)) hsnK0
    obtain ⟨hs, -⟩ := isSimpleGroup_of_isLThreeFour c.L34_inf
    have htop : barX 3 Y K0 = ⊤ := c.layer_data.2.1
    have hsimple : IsSimpleGroup ↥(barX 3 Y K0) := by
      rw [htop]
      exact (Subgroup.topEquiv (G := ↥Y ⧸ GLAPPrimeCore 3 ↥Y)).symm.isSimpleGroup_congr.1 hs
    have hdiv : 3 ∣ Nat.card (barX 3 Y K0) := by
      rw [htop, Subgroup.card_top, card_eq_of_isLThreeFour c.L34_inf]
      norm_num
    have hbar : barX 3 Y Z = barX 3 Y K0 := barX_closure_three_eq hK0Y hsimple hdiv
    by_contra hne
    exact c.layer_data.1.2.2.2 Z (lt_of_le_of_ne hZK0 hne) hsnZ hbar
  apply le_antisymm
  · intro w hw
    obtain ⟨a, ha, haK0, rfl⟩ := exists_mem_of_mem_barX hw
    have haZ : a ∈ Z := hZeq ▸ haK0
    have key : ∀ b : G, b ∈ Z → ∀ hb : b ∈ N, mkN N b hb ∈ Subgroup.closure
        {g | g ∈ barX 3 N K0 ∧ IsPGroup 3 (Subgroup.zpowers g)} := by
      intro b hb
      refine Subgroup.closure_induction
        (p := fun b _ => ∀ hb : b ∈ N, mkN N b hb ∈ Subgroup.closure
          {g | g ∈ barX 3 N K0 ∧ IsPGroup 3 (Subgroup.zpowers g)})
        (fun g hg hgN => ?_) (fun _ => ?_) (fun u v hu hv ihu ihv huvN => ?_)
        (fun u hu ihu huN => ?_) hb
      · refine Subgroup.subset_closure ⟨mkN_mem_barX hgN hg.1, ?_⟩
        exact (isPGroup_barX hg.2).to_le
          (Subgroup.zpowers_le.2 (mkN_mem_barX hgN (Subgroup.mem_zpowers g)))
      · rw [mkN_one]; exact one_mem _
      · have huN : u ∈ N := hK0N (hZK0 hu)
        have hvN : v ∈ N := hK0N (hZK0 hv)
        exact mul_mem (ihu huN) (ihv hvN)
      · have huN' : u ∈ N := by simpa using N.inv_mem huN
        have e : mkN N u⁻¹ huN = (mkN N u huN')⁻¹ := rfl
        rw [e]
        exact inv_mem (ihu huN')
    exact key a haZ ha
  · exact (Subgroup.closure_le _).2 fun g hg => hg.1

theorem K0b_L34 (c : Ctx75 B N K x) :
    IsLThreeFour (↥(barX 3 N (GLAPLayer 3 (K ⊓ N))) ⧸
      GLAPPrimeCore 3 ↥(barX 3 N (GLAPLayer 3 (K ⊓ N)))) := by
  set Y := K ⊓ N with hY
  set K0 := GLAPLayer 3 Y with hK0
  have hbar : IsLThreeFour ↥(barX 3 Y K0) := by
    rw [c.layer_data.2.1]
    exact IsLThreeFour.of_mulEquiv
      (Subgroup.topEquiv (G := ↥Y ⧸ GLAPPrimeCore 3 ↥Y)).symm c.L34_inf
  have hK0L : IsLThreeFour (↥K0 ⧸ GLAPPrimeCore 3 ↥K0) :=
    IsLThreeFour.of_mulEquiv
      (quotEquivBarX Nat.prime_three c.layer_data.1.1 c.layer_data.1.2.1).symm hbar
  exact isLThreeFour_barX_quot c.K0_le_N hK0L

theorem K0b_norm (c : Ctx75 B N K x) :
    Subgroup.centralizer ({mkN N x c.hxN} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) ≤
      Subgroup.normalizer (barX 3 N (GLAPLayer 3 (K ⊓ N)) : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
  have hx3 : x ^ 3 = 1 := c.bone.1.1.2 x c.hxB
  rw [centralizer_mkN_singleton c.hxN hx3]
  refine barX_le_normalizer ?_
  intro g hg
  exact Sec7.mem_normalizer_glaPLayer (Sec7.inf_normalizer_le_normalizer_inf K N
    ⟨c.hCx hg.2, Subgroup.le_normalizer hg.1⟩)

theorem K0b_cent (c : Ctx75 B N K x) :
    barX 3 N (GLAPLayer 3 (K ⊓ N)) ≤
      Subgroup.centralizer ({mkN N x c.hxN} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.1 hh]
  obtain ⟨a, ha, haK0, rfl⟩ := exists_mem_of_mem_barX hz
  have haK : a ∈ K := (c.layer_data.1.1 haK0).1
  have e : x * a = a * x := by
    have := c.hxK.1 haK
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm
  exact congrArg (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)) (Subtype.ext e)

end Ctx75

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
