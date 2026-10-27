module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Alt
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Spor

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement
open CFSG.HardMathSupport.Curtis.Coordinator.Plane
  (conjL conjL_apply conjHom quotAut quotAut_mk quotAutHom)

section SporStruct

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem aut_three_inner_of_outer_le_two {S : Type} [Group S] [Finite S]
    (hout : Nat.card (Outer S) ≤ 2) :
    ∀ ψ : MulAut S, ψ ^ 3 = 1 → ∃ a : S, ψ = MulAut.conj a := by
  intro φ hφ
  obtain ⟨q, hqdef⟩ : ∃ q : Outer S, q = QuotientGroup.mk φ := ⟨_, rfl⟩
  have hq3 : q ^ 3 = 1 := by
    have h := map_pow (QuotientGroup.mk' (inner S)) φ 3
    rw [hφ, map_one] at h
    rw [hqdef]
    exact h.symm
  have h1 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
  have hpos : 0 < Nat.card (Outer S) := Nat.card_pos
  have h2 : orderOf q ≤ 2 := (Nat.le_of_dvd hpos (orderOf_dvd_natCard q)).trans hout
  have h3 : orderOf q = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact h
    · omega
  have hq1 : q = 1 := orderOf_eq_one_iff.mp h3
  rw [hqdef] at hq1
  have hmem : φ ∈ inner S := (QuotientGroup.eq_one_iff (N := inner S) φ).mp hq1
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, hg.symm⟩

theorem T29Setup.exists_mul_of_inner (h : T29Setup X L x) {S : Type} [Group S]
    (e : (↥L ⧸ center ↥L) ≃* S)
    (hin : ∀ ψ : MulAut S, ψ ^ 3 = 1 → ∃ a : S, ψ = MulAut.conj a) {g : X} (hg : g ^ 3 = 1) :
    ∃ l ∈ L, ∃ c ∈ centralizer (L : Set X), g = l * c := by
  haveI hLn : L.Normal := h.normal
  have hN : ∀ y : X, y ∈ Subgroup.normalizer (L : Set X) := by
    intro y
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact Subgroup.mem_top y
  obtain ⟨θ, hθdef⟩ : ∃ θ : MulAut ↥L, θ = conjL g (hN g) := ⟨_, rfl⟩
  have hT : ∀ k : ↥L, ((θ k : ↥L) : X) = g * (k : X) * g⁻¹ := by
    intro k
    rw [hθdef]
    rfl
  have hθ3 : θ ^ 3 = 1 := by
    have hg3 : (⟨g, hN g⟩ : ↥(Subgroup.normalizer (L : Set X))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hg)
    have h1 := map_pow (conjHom L) (⟨g, hN g⟩ : ↥(Subgroup.normalizer (L : Set X))) 3
    rw [hg3, map_one] at h1
    rw [hθdef]
    exact h1.symm
  have hq3 : quotAut θ ^ 3 = 1 := by
    have h1 := map_pow (quotAutHom L) θ 3
    rw [hθ3, map_one] at h1
    exact h1.symm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulAut S,
      ψ = MulAut.congr e (quotAut θ) := ⟨_, rfl⟩
  have hψ3 : ψ ^ 3 = 1 := by
    have h1 := map_pow (MulAut.congr e) (quotAut θ) 3
    rw [hq3, map_one] at h1
    rw [hψ]
    exact h1.symm
  obtain ⟨a, ha⟩ := hin ψ hψ3
  have hψapp : ∀ l : ↥L, ψ (e (l : ↥L ⧸ center ↥L)) = e ((θ l : ↥L) : ↥L ⧸ center ↥L) := by
    intro l
    simp only [hψ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      quotAut_mk]
  obtain ⟨l₀, hl₀⟩ := QuotientGroup.mk_surjective (e.symm a)
  have hl₀a : e (l₀ : ↥L ⧸ center ↥L) = a := by
    rw [hl₀, MulEquiv.apply_symm_apply]
  have hkey : ∀ l : ↥L, (θ l)⁻¹ * (l₀ * l * l₀⁻¹) ∈ center ↥L := by
    intro l
    have h1 := hψapp l
    rw [ha, MulAut.conj_apply, ← hl₀a] at h1
    have h2 : ((θ l : ↥L) : ↥L ⧸ center ↥L) = ((l₀ * l * l₀⁻¹ : ↥L) : ↥L ⧸ center ↥L) := by
      apply e.injective
      rw [← h1]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
    exact QuotientGroup.eq.mp h2
  obtain ⟨c, hc_def⟩ : ∃ c : X, c = (l₀ : X)⁻¹ * g := ⟨_, rfl⟩
  obtain ⟨α, hα_def⟩ : ∃ α : MulAut ↥L, α = conjL c (hN c) := ⟨_, rfl⟩
  have hαapp : ∀ k : ↥L, ((α k : ↥L) : X) = c * (k : X) * c⁻¹ := by
    intro k
    rw [hα_def]
    rfl
  have hα : ∀ k : ↥L, α k * k⁻¹ ∈ center ↥L := by
    intro k
    have hu := hkey k
    have hU : (((θ k)⁻¹ * (l₀ * k * l₀⁻¹) : ↥L) : X)
        = ((θ k : ↥L) : X)⁻¹ * ((l₀ : X) * (k : X) * (l₀ : X)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hUL : (l₀ : X) * (((θ k)⁻¹ * (l₀ * k * l₀⁻¹) : ↥L) : X)
        = (((θ k)⁻¹ * (l₀ * k * l₀⁻¹) : ↥L) : X) * (l₀ : X) := by
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hu l₀)
      simpa only [Subgroup.coe_mul] using h1
    have hUK : (k : X) * (((θ k)⁻¹ * (l₀ * k * l₀⁻¹) : ↥L) : X)
        = (((θ k)⁻¹ * (l₀ * k * l₀⁻¹) : ↥L) : X) * (k : X) := by
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hu k)
      simpa only [Subgroup.coe_mul] using h1
    have hX := conj_alg_identity g (l₀ : X) (k : X) ((θ k : ↥L) : X)
      (((θ k)⁻¹ * (l₀ * k * l₀⁻¹) : ↥L) : X) (hT k) hU hUL hUK
    have heq : α k * k⁻¹ = ((θ k)⁻¹ * (l₀ * k * l₀⁻¹))⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hαapp, hc_def]
      exact hX
    rw [heq]
    exact inv_mem hu
  have hfix := eq_one_of_trivial_mod_center h.comp.2.2.1 α.toMonoidHom hα
  have hcent : c ∈ centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hX : c * m * c⁻¹ = m := by
      have h1 : ((α ⟨m, hm⟩ : ↥L) : X) = c * m * c⁻¹ := hαapp ⟨m, hm⟩
      have h2 : ((α ⟨m, hm⟩ : ↥L) : X) = m := congrArg Subtype.val (hfix ⟨m, hm⟩)
      exact h1.symm.trans h2
    calc m * c = (c * m * c⁻¹) * c := by rw [hX]
      _ = c * m := by group
  refine ⟨(l₀ : X), l₀.2, c, hcent, ?_⟩
  rw [hc_def]
  group

def commutatorSubgroupLocal {P : Subgroup X} {z : X} (hzc : ∀ y ∈ P, z * y = y * z) (x : X) :
    Subgroup X where
  carrier := {v | v ∈ P ∧ x * v * x⁻¹ * v⁻¹ ∈ zpowers z}
  one_mem' := ⟨P.one_mem, by simp [one_mem]⟩
  mul_mem' := by
    rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
    refine ⟨P.mul_mem haP hbP, ?_⟩
    have hcb := conj_eq_of_mem_zpowers_central hzc haP hb
    have h1 : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [h1, hcb]
    exact mul_mem ha hb
  inv_mem' := by
    rintro a ⟨haP, ha⟩
    refine ⟨P.inv_mem haP, ?_⟩
    have h1 : x * a⁻¹ * x⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ := by group
    rw [h1, conj_eq_of_mem_zpowers_central hzc (P.inv_mem haP) (inv_mem ha)]
    exact inv_mem ha

theorem T29Setup.isCyclic_pCore_of_center_cyclic (h : T29Setup X L x)
    (hZc : IsCyclic ↥(center ↥L)) (hZ : center ↥L ≠ ⊥) : IsCyclic ↥(CFSG.pCore 3 X) := by
  by_contra hnc
  haveI hLn : L.Normal := h.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.ord] at this
  obtain ⟨P, hxP⟩ : ∃ P : Sylow 3 X, x ∈ (P : Subgroup X) := by
    have hp : IsPGroup 3 (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.ord]; norm_num)
    obtain ⟨P, hP⟩ := hp.exists_le_sylow
    exact ⟨P, hP (mem_zpowers x)⟩
  obtain ⟨z, hz⟩ := h.exists_omegaCentral hxP
  have hP3 : IsPGroup 3 (P : Subgroup X) := P.isPGroup'
  set O : Subgroup X := CFSG.pCore 3 X with hO
  haveI hOn : O.Normal := CFSG.pCore_normal
  have hOP : O ≤ (P : Subgroup X) := pCore_le_sylow P
  have hOnorm : (P : Subgroup X) ≤ normalizer (O : Set X) := le_normalizer_of_normal
  obtain ⟨U₂, hU₂O, hU₂el, hU₂9, hU₂n⟩ := exists_normal_E9 hP3 hOP hOnorm hnc
  have hRnc := h.not_isCyclic_inf_sylow hZ hz
  have hRnorm : (P : Subgroup X) ≤ normalizer (((P : Subgroup X) ⊓ L : Subgroup X) : Set X) :=
    fun g hg => inf_normalizer_le_normalizer_inf ⟨le_normalizer hg, le_normalizer_of_normal hg⟩
  obtain ⟨U₁, hU₁R, hU₁el, hU₁9, hU₁n⟩ := exists_normal_E9 hP3 inf_le_left hRnorm hRnc
  have hU₁P : U₁ ≤ P := hU₁R.trans inf_le_left
  have hU₁L : U₁ ≤ L := hU₁R.trans inf_le_right
  have hU₂P : U₂ ≤ P := hU₂O.trans hOP
  have hz1 : z ≠ 1 := by
    intro h1
    have := hz.order
    rw [h1, orderOf_one] at this
    omega
  have hz3 : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.order] at this
  have hne1 : U₁ ≠ ⊥ := by
    intro h1
    rw [h1, Subgroup.card_bot] at hU₁9
    omega
  have hne2 : U₂ ≠ ⊥ := by
    intro h1
    rw [h1, Subgroup.card_bot] at hU₂9
    omega
  have hzU₁ : z ∈ U₁ := hz.mem_of_normal hP3 hU₁P hU₁n hne1
  have hzU₂ : z ∈ U₂ := hz.mem_of_normal hP3 hU₂P hU₂n hne2
  have hcomm : ∀ l ∈ L, ∀ o ∈ O, l * o = o * l :=
    commute_of_inf_le_center h.comp.2.2 (fun g hgL hgO l hl => h.pCore_inf_commute g hgL hgO l hl)
  have hinf : Nat.card (U₁ ⊓ U₂ : Subgroup X) = 3 := by
    have hge : 3 ≤ Nat.card (U₁ ⊓ U₂ : Subgroup X) := by
      have hle : zpowers z ≤ U₁ ⊓ U₂ := zpowers_le.mpr ⟨hzU₁, hzU₂⟩
      have h1 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, hz.order] at h1
      exact h1
    have hle : Nat.card (U₁ ⊓ U₂ : Subgroup X) ≤ 3 := by
      haveI hcyc : IsCyclic ↥(center ↥L) := hZc
      set ZL : Subgroup X := (center ↥L).map L.subtype with hZL
      haveI : IsCyclic ↥ZL :=
        isCyclic_of_surjective (Subgroup.equivMapOfInjective (center ↥L) L.subtype
          L.subtype_injective).toMonoidHom (Subgroup.equivMapOfInjective (center ↥L)
          L.subtype L.subtype_injective).surjective
      have hWZ : U₁ ⊓ U₂ ≤ ZL := by
        intro g hg
        have hgL : g ∈ L := hU₁L hg.1
        have hgO : g ∈ O := hU₂O hg.2
        refine ⟨⟨g, hgL⟩, Subgroup.mem_center_iff.mpr fun l => ?_, rfl⟩
        have := h.pCore_inf_commute g hgL hgO l l.2
        exact Subtype.ext this
      haveI : IsCyclic ↥(U₁ ⊓ U₂) := isCyclic_of_le hWZ
      refine card_le_three_of_cyclic (W := ↥(U₁ ⊓ U₂)) ?_
      intro w
      have hw : (w : X) ∈ U₁ := w.2.1
      have := hU₁el.2 (w : X) hw
      exact Subtype.ext (by simpa using this)
    omega
  obtain ⟨hVel, hV27⟩ := isElemAbelian_sup_card_27 hU₁el hU₂el hU₁9 hU₂9
    (fun a ha b hb => hcomm a (hU₁L ha) b (hU₂O hb)) hinf
  have hVP : U₁ ⊔ U₂ ≤ P := sup_le hU₁P hU₂P
  have hxV : x ∈ normalizer ((U₁ ⊔ U₂ : Subgroup X) : Set X) :=
    normalizer_sup_of_le hU₁n hU₂n hxP
  have hzV : ∀ v ∈ U₁ ⊔ U₂, z * v = v * z := fun v hv => hz.central v (hVP hv)
  have hK : U₁ ⊔ U₂ ≤ commutatorSubgroupLocal hz.central x := by
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · exact ⟨hU₁P hu, hz.commutator_mem hP3 hU₁P hU₁el hU₁9 hzU₁ hU₁n x hxP u hu⟩
    · exact ⟨hU₂P hu, hz.commutator_mem hP3 hU₂P hU₂el hU₂9 hzU₂ hU₂n x hxP u hu⟩
  have hcommV : ∀ v ∈ U₁ ⊔ U₂, x * v * x⁻¹ * v⁻¹ ∈ zpowers z := fun v hv => (hK hv).2
  have h3 := three_le_pRank_centralizer_of_unipotent hx3 hz1 hz3 hVel hV27 hzV hxV hcommV
  have h2 := h.cent
  omega

theorem T29Setup.mem_of_triple_cover (h : T29Setup X L x) (hO : IsCyclic ↥(CFSG.pCore 3 X))
    (hcard3 : Nat.card ↥(center ↥L) = 3)
    (hdec : ∀ g : X, g ^ 3 = 1 → ∃ l ∈ L, ∃ c ∈ centralizer (L : Set X), g = l * c)
    (hfus : ∀ l : ↥L, l ∉ center ↥L → l ^ 3 ∈ center ↥L → l ^ 3 = 1)
    {g : X} (hg : g ^ 3 = 1) : g ∈ L := by
  haveI hLn : L.Normal := h.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨l, hl, c, hc, rfl⟩ := hdec g hg
  set Zc : Subgroup X := (center ↥L).map L.subtype with hZc
  have hZcard : Nat.card Zc = 3 := by
    rw [hZc, Subgroup.card_map_of_injective L.subtype_injective]
    exact hcard3
  have hZcpg : IsPGroup 3 Zc := IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
  haveI hZcn : Zc.Normal := normal_map_center_subtype L
  have hZO : Zc ≤ CFSG.pCore 3 X := normal_pGroup_le_pCore 3 Zc hZcn hZcpg
  have hZL : Zc ≤ L := Subgroup.map_subtype_le _
  have hZcube : ∀ z ∈ Zc, z ^ 3 = 1 := by
    intro z hz
    have h1 : (⟨z, hz⟩ : Zc) ^ Nat.card Zc = 1 := pow_card_eq_one'
    rw [hZcard] at h1
    exact congrArg Subtype.val h1
  have hC' := Subgroup.mem_centralizer_iff.mp hc
  have hcomm : Commute l c := hC' l hl
  have hmul : l ^ 3 * c ^ 3 = 1 := by
    rw [← hcomm.mul_pow]
    exact hg
  have hc3eq : c ^ 3 = (l ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hmul
  have hc3L : c ^ 3 ∈ L := by
    rw [hc3eq]
    exact L.inv_mem (L.pow_mem hl 3)
  have hc3Z : c ^ 3 ∈ Zc := by
    refine ⟨⟨c ^ 3, hc3L⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp ((centralizer (L : Set X)).pow_mem hc 3) y y.2
    simpa using this
  have hc9 : c ^ 9 = 1 := by
    have := hZcube _ hc3Z
    rw [← pow_mul] at this
    exact this
  have hcpg : IsPGroup 3 (zpowers c) := by
    have hdvd : orderOf c ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hc9)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hcO : c ∈ CFSG.pCore 3 X :=
    h.le_pCore_of_centralizer hO hcpg (Subgroup.zpowers_le.mpr hc) (Subgroup.mem_zpowers c)
  by_cases hc3 : c ^ 3 = 1
  · have hcL : c ∈ L := by
      by_cases hc1 : c = 1
      · rw [hc1]
        exact L.one_mem
      · have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
        obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Zc) 3 (by rw [hZcard])
        have hζO : (ζ : X) ∈ CFSG.pCore 3 X := hZO ζ.2
        have hmem := mem_zpowers_of_cyclic (W := ↥(CFSG.pCore 3 X)) (a := ⟨c, hcO⟩)
          (b := ⟨ζ, hζO⟩) (Subtype.ext (by simpa using hc3))
          (by rw [← Subgroup.orderOf_coe]; simpa using hζ)
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have hck : c = (ζ : X) ^ k := by
          have := congrArg Subtype.val hk
          simpa using this.symm
        rw [hck]
        exact zpow_mem (hZL ζ.2) k
    exact L.mul_mem hl hcL
  · exfalso
    have hlZ : l ^ 3 ∈ Zc := by
      have : l ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hmul
      rw [this]
      exact Zc.inv_mem hc3Z
    have hl3 : (⟨l, hl⟩ : ↥L) ^ 3 ∈ center ↥L := by
      obtain ⟨z, hz, hzl⟩ := hlZ
      have : (⟨l, hl⟩ : ↥L) ^ 3 = z := by
        apply Subtype.ext
        simpa using hzl.symm
      rw [this]
      exact hz
    have hlnot : (⟨l, hl⟩ : ↥L) ∉ center ↥L := by
      intro hlc
      have hlmem : l ∈ Zc := ⟨⟨l, hl⟩, hlc, rfl⟩
      have h1 := hZcube l hlmem
      apply hc3
      rw [hc3eq, h1, inv_one]
    have h1 := hfus ⟨l, hl⟩ hlnot hl3
    apply hc3
    rw [hc3eq]
    have : l ^ 3 = 1 := congrArg Subtype.val h1
    rw [this, inv_one]

theorem T29Setup.false_of_triple_cover (h : T29Setup X L x) (hO : IsCyclic ↥(CFSG.pCore 3 X))
    (hcard3 : Nat.card ↥(center ↥L) = 3)
    (hdec : ∀ g : X, g ^ 3 = 1 → ∃ l ∈ L, ∃ c ∈ centralizer (L : Set X), g = l * c)
    (hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L))
    (hcent : ∀ l : ↥L, l ∉ center ↥L → l ^ 3 ∈ center ↥L →
      l ^ 3 = 1 ∧ 3 ≤ CFSG.Open.pRank 3 (centralizer ({l} : Set ↥L))) : False := by
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.ord] at this
  have hxL : x ∈ L :=
    h.mem_of_triple_cover hO hcard3 hdec (fun l hl1 hl2 => (hcent l hl1 hl2).1) hx3
  have hcentr := h.cent
  set xL : ↥L := ⟨x, hxL⟩ with hxLdef
  by_cases hxc : xL ∈ center ↥L
  · have hLC : L ≤ centralizer ({x} : Set X) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      have := Subgroup.mem_center_iff.mp hxc ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤
        CFSG.Open.pRank 3 ((⊤ : Subgroup ↥L).map L.subtype) :=
      CFSG.SectionRank.pRank_le_map (by norm_num) L.subtype L.subtype_injective ⊤
    have h2 : CFSG.Open.pRank 3 ((⊤ : Subgroup ↥L).map L.subtype) ≤
        CFSG.Open.pRank 3 (centralizer ({x} : Set X)) :=
      pRank_mono 3 (by norm_num) (by
        rintro _ ⟨y, -, rfl⟩
        exact hLC y.2)
    omega
  · have hx3L : xL ^ 3 = 1 := Subtype.ext (by simpa [hxLdef] using hx3)
    obtain ⟨-, hr⟩ := hcent xL hxc (by rw [hx3L]; exact one_mem _)
    have h1 : CFSG.Open.pRank 3 (centralizer ({xL} : Set ↥L)) ≤
        CFSG.Open.pRank 3 ((centralizer ({xL} : Set ↥L)).map L.subtype) :=
      CFSG.SectionRank.pRank_le_map (by norm_num) L.subtype L.subtype_injective _
    have h2 : CFSG.Open.pRank 3 ((centralizer ({xL} : Set ↥L)).map L.subtype) ≤
        CFSG.Open.pRank 3 (centralizer ({x} : Set X)) :=
      pRank_mono 3 (by norm_num) (by
        rintro _ ⟨y, hy, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.mp hz]
        have := Subgroup.mem_centralizer_iff.mp hy xL (Set.mem_singleton _)
        exact congrArg Subtype.val this)
    omega

theorem T29Setup.false_of_abelian_bound (h : T29Setup X L x) (hO : IsCyclic ↥(CFSG.pCore 3 X))
    (hcard3 : Nat.card ↥(center ↥L) = 3)
    (hdec : ∀ g : X, g ^ 3 = 1 → ∃ l ∈ L, ∃ c ∈ centralizer (L : Set X), g = l * c)
    (hA : ∀ A : Subgroup ↥L, IsPGroup 3 A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      Nat.card A ≤ 9) : False := by
  haveI hLn : L.Normal := h.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank := h.pRank_top_eq
  obtain ⟨E, -, hEel, hE27⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  rw [hrank] at hE27
  have hE27' : Nat.card E = 27 := by rw [hE27]; norm_num
  set C : Subgroup X := centralizer (L : Set X) with hC
  have hLE : ∀ g ∈ E, ∃ l ∈ L, ∃ c ∈ C, g = l * c := fun g hg => hdec g (hEel.2 g hg)
  have hEp : IsPGroup 3 E := CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 3 E hEel
  have hEC : Nat.card (E ⊓ C : Subgroup X) ≤ 3 := by
    have hle : (E ⊓ C : Subgroup X) ≤ CFSG.pCore 3 X :=
      h.le_pCore_of_centralizer hO (hEp.to_le inf_le_left) inf_le_right
    haveI : IsCyclic ↥(CFSG.pCore 3 X) := hO
    haveI : IsCyclic ↥(E ⊓ C : Subgroup X) := isCyclic_of_le hle
    refine card_le_three_of_cyclic (W := ↥(E ⊓ C : Subgroup X)) ?_
    intro w
    have := hEel.2 (w : X) w.2.1
    exact Subtype.ext (by simpa using this)
  have hZ' : Nat.card (L ⊓ C : Subgroup X) = 3 := by
    have hEq : (L ⊓ C : Subgroup X) = (center ↥L).map L.subtype := by
      ext g
      constructor
      · rintro ⟨hgL, hgC⟩
        refine ⟨⟨g, hgL⟩, Subgroup.mem_center_iff.mpr fun l => ?_, rfl⟩
        have := Subgroup.mem_centralizer_iff.mp hgC l l.2
        exact Subtype.ext this
      · rintro ⟨c, hc, rfl⟩
        refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
        have := Subgroup.mem_center_iff.mp hc ⟨l, hl⟩
        exact congrArg Subtype.val this
    rw [hEq, Subgroup.card_map_of_injective L.subtype_injective]
    exact hcard3
  have hC3 : ∀ B : Subgroup X, B ≤ C → IsPGroup 3 B → ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    intro B hBC hB b hb b' hb'
    have hle : B ≤ CFSG.pCore 3 X := h.le_pCore_of_centralizer hO hB hBC
    haveI : IsCyclic ↥(CFSG.pCore 3 X) := hO
    have := (inferInstance : IsMulCommutative ↥(CFSG.pCore 3 X)).is_comm.comm
      (⟨b, hle hb⟩ : ↥(CFSG.pCore 3 X)) ⟨b', hle hb'⟩
    exact congrArg Subtype.val this
  obtain ⟨A, hAL, hA3, hAab, hA27⟩ := exists_abelian_of_elemAbelian_cover hLE hEC hE27' hEel hZ'
    hC3
  have hAp : IsPGroup 3 ↥(A.subgroupOf L) :=
    hA3.of_injective (Subgroup.subgroupOfEquivOfLe hAL).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAL).injective
  have hbound := hA (A.subgroupOf L) hAp (by
    intro a ha b hb
    have := hAab a ha b hb
    exact Subtype.ext this)
  have hcardA : Nat.card ↥(A.subgroupOf L) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  omega

theorem T29Setup.three_le_pRank_quotient (h : T29Setup X L x) (hZ : center ↥L = ⊥)
    (hout : Nat.card (Outer (↥L ⧸ center ↥L)) ≤ 2) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ center ↥L)) := by
  haveI hLn : L.Normal := h.normal
  have hC : centralizer (L : Set X) = ⊥ := h.centralizer_eq_bot hZ
  have hinj : Function.Injective (MulAut.conjNormal : X →* MulAut L) :=
    conjNormal_injective_of_centralizer_eq_bot L hC
  have h1 := CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num)
    (MulAut.conjNormal : X →* MulAut L) hinj
  have h2 := CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_mulAut_le_centerQuotient_of_outer
    h.comp.2.2 Nat.prime_three (by norm_num) hout
  have h3 := h.pRank_top_eq
  omega

theorem T29Setup.pRank_quotient_le_three (h : T29Setup X L x) (hZ : center ↥L = ⊥) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ center ↥L)) ≤ 3 := by
  let hψ : (↥L ⧸ center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) hψ
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤
      CFSG.Open.pRank 3 ((⊤ : Subgroup ↥L).map L.subtype) :=
    CFSG.SectionRank.pRank_le_map (by norm_num) L.subtype L.subtype_injective ⊤
  have h3 : CFSG.Open.pRank 3 ((⊤ : Subgroup ↥L).map L.subtype) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup X) := pRank_mono 3 (by norm_num) le_top
  have h4 := h.pRank_top_eq
  omega

theorem T29Setup.pRank_quotient_eq_three (h : T29Setup X L x) (hZ : center ↥L = ⊥)
    (hout : Nat.card (Outer (↥L ⧸ center ↥L)) ≤ 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ center ↥L)) = 3 :=
  le_antisymm (h.pRank_quotient_le_three hZ) (h.three_le_pRank_quotient hZ hout)

theorem T29Setup.false_of_center_bot_cent (h : T29Setup X L x) (hZ : center ↥L = ⊥)
    (hdec : ∀ g : X, g ^ 3 = 1 → ∃ l ∈ L, ∃ c ∈ centralizer (L : Set X), g = l * c)
    {S : Type} [Group S] [Finite S] (e : (↥L ⧸ center ↥L) ≃* S)
    (hJ : ∀ y : S, orderOf y = 3 → 3 ≤ CFSG.Open.pRank 3 (centralizer ({y} : Set S))) :
    False := by
  haveI hLn : L.Normal := h.normal
  have hC : centralizer (L : Set X) = ⊥ := h.centralizer_eq_bot hZ
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.ord] at this
  obtain ⟨l, hl, c, hc, hxlc⟩ := hdec x hx3
  rw [hC, Subgroup.mem_bot] at hc
  have hxl : x = l := by rw [hxlc, hc, mul_one]
  have hxL : x ∈ L := hxl ▸ hl
  let e' : ↥L ≃* S := (QuotientGroup.quotientBot (G := ↥L)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans e)
  set xL : ↥L := ⟨x, hxL⟩ with hxLdef
  have hord : orderOf (e' xL) = 3 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact h.ord
  have hr := hJ (e' xL) hord
  let f : S →* X := L.subtype.comp e'.symm.toMonoidHom
  have hfinj : Function.Injective f := L.subtype_injective.comp e'.symm.injective
  have hfx : f (e' xL) = x := by
    simp [f, hxLdef]
  have h1 : CFSG.Open.pRank 3 (centralizer ({e' xL} : Set S)) ≤
      CFSG.Open.pRank 3 ((centralizer ({e' xL} : Set S)).map f) :=
    CFSG.SectionRank.pRank_le_map (by norm_num) f hfinj _
  have h2 : CFSG.Open.pRank 3 ((centralizer ({e' xL} : Set S)).map f) ≤
      CFSG.Open.pRank 3 (centralizer ({x} : Set X)) :=
    pRank_mono 3 (by norm_num) (by
      rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz, ← hfx]
      have := Subgroup.mem_centralizer_iff.mp hw (e' xL) (Set.mem_singleton _)
      rw [← map_mul, ← map_mul, this])
  have := h.cent
  omega

theorem T29Setup.pRank_component_le (h : T29Setup X L x) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 3 := by
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤
      CFSG.Open.pRank 3 ((⊤ : Subgroup ↥L).map L.subtype) :=
    CFSG.SectionRank.pRank_le_map (by norm_num) L.subtype L.subtype_injective ⊤
  have h3 : CFSG.Open.pRank 3 ((⊤ : Subgroup ↥L).map L.subtype) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup X) := pRank_mono 3 (by norm_num) le_top
  have h4 := h.pRank_top_eq
  omega

theorem T29Setup.isPerfect (h : T29Setup X L x) : Group.IsPerfect ↥L :=
  Group.isPerfect_def.mpr h.comp.2.2.1

end SporStruct


theorem pRank_centralizer_le_of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (φ : A ≃* B) (a : A) :
    CFSG.Open.pRank 3 (centralizer ({a} : Set A)) ≤
      CFSG.Open.pRank 3 (centralizer ({φ a} : Set B)) := by
  have h1 : CFSG.Open.pRank 3 (centralizer ({a} : Set A)) ≤
      CFSG.Open.pRank 3 ((centralizer ({a} : Set A)).map φ.toMonoidHom) :=
    CFSG.SectionRank.pRank_le_map (by norm_num) φ.toMonoidHom φ.injective _
  refine h1.trans (pRank_mono 3 (by norm_num) ?_)
  rintro _ ⟨w, hw, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff.mp hz]
  have := Subgroup.mem_centralizer_iff.mp hw a (Set.mem_singleton _)
  simpa using congrArg φ this

theorem pRank_centralizer_eq_of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (φ : A ≃* B) (a : A) :
    CFSG.Open.pRank 3 (centralizer ({a} : Set A)) =
      CFSG.Open.pRank 3 (centralizer ({φ a} : Set B)) := by
  refine le_antisymm (pRank_centralizer_le_of_mulEquiv φ a) ?_
  have := pRank_centralizer_le_of_mulEquiv φ.symm (φ a)
  simpa using this

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
