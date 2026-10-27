module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQ49
public import CFSG.LocalAnalysis.EvenBN.G2.BCriterion

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

namespace Q52

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem card_coe_mul_mul_card_inf (A B : Subgroup G) :
    Nat.card ((A : Set G) * (B : Set G)) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient B (A : Set G)
  have himg : Nat.card ((A : Set G).image ((↑) : G → G ⧸ B)) = B.relIndex A := by
    have horb : MulAction.orbit A ((1 : G) : G ⧸ B) = (A : Set G).image ((↑) : G → G ⧸ B) := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨(a : G), a.2, by simp [Subgroup.smul_def]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, by simp [Subgroup.smul_def]⟩
    have hstab : MulAction.stabilizer A ((1 : G) : G ⧸ B) = B.subgroupOf A := by
      ext a
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have : (a • ((1 : G) : G ⧸ B)) = ((a : G) : G ⧸ B) := by
        simp [Subgroup.smul_def]
      rw [this, QuotientGroup.eq]
      constructor
      · intro h
        have := B.inv_mem h
        simpa using this
      · intro h
        have := B.inv_mem h
        simpa using this
    have := MulAction.index_stabilizer A ((1 : G) : G ⧸ B)
    rw [hstab] at this
    rw [← horb, Nat.card_coe_set_eq, ← this]
    rfl
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_comm B A] at h2
  rw [h1, himg]
  calc Nat.card B * B.relIndex A * Nat.card (A ⊓ B : Subgroup G)
      = Nat.card B * (B.relIndex A * Nat.card (A ⊓ B : Subgroup G)) := by ring
    _ = Nat.card A * Nat.card B := by rw [h2]; ring

theorem commutator_mem_of_coprime_trivial {P A Y Z : Subgroup G}
    (hsolv : Group.IsSolvable P) (hcop : (Nat.card A).Coprime (Nat.card P))
    (hAP : A ≤ normalizer (P : Set G)) (hAY : A ≤ normalizer (Y : Set G))
    (hAZ : A ≤ normalizer (Z : Set G)) (hPY : P ≤ normalizer (Y : Set G))
    (hPZ : P ≤ normalizer (Z : Set G)) (hYZ : Y ≤ normalizer (Z : Set G))
    (hA : ∀ a ∈ A, ∀ y ∈ Y, y⁻¹ * (a * y * a⁻¹) ∈ Z)
    (hC : ∀ c ∈ P ⊓ centralizer (A : Set G), ∀ y ∈ Y, c * y * c⁻¹ * y⁻¹ ∈ Z) :
    ∀ x ∈ P, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ Z := by
  have hK₀ : ∀ g ∈ P, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := fun g hg y hy =>
    (mem_normalizer_iff.1 (hPY hg) y).1 hy
  have hB : ∀ g ∈ P, ∀ b ∈ Z, g * b * g⁻¹ ∈ Z := fun g hg b hb =>
    (mem_normalizer_iff.1 (hPZ hg) b).1 hb
  set N := Common.centralizerMod P Y Z hK₀ hB with hNdef
  intro x hx y hy
  have hfix : ∀ j ∈ A, x⁻¹ * (j * x * j⁻¹) ∈ N := by
    intro j hj
    have hx' : j * x * j⁻¹ ∈ P := (mem_normalizer_iff.1 (hAP hj) x).1 hx
    refine ⟨mul_mem (inv_mem hx) hx', fun y hy => ?_⟩
    have ha := hA _ (inv_mem hj) y hy
    rw [inv_inv] at ha
    have hb := hA j hj (x * y * x⁻¹) (hK₀ x hx y hy)
    have ha' : j * (x * (y⁻¹ * (j⁻¹ * y * j)) * x⁻¹) * j⁻¹ ∈ Z :=
      (mem_normalizer_iff.1 (hAZ hj) _).1 (hB x hx _ ha)
    have key : x⁻¹ * (j * x * j⁻¹) * y * (x⁻¹ * (j * x * j⁻¹))⁻¹ * y⁻¹ =
        y * (x⁻¹ * (((x * y * x⁻¹)⁻¹ * (j * (x * y * x⁻¹) * j⁻¹)) *
          (j * (x * (y⁻¹ * (j⁻¹ * y * j)) * x⁻¹) * j⁻¹)) * x) * y⁻¹ := by group
    rw [key]
    have h1 := (mem_normalizer_iff.1 (inv_mem (hPZ hx)) _).1 (mul_mem hb ha')
    rw [inv_inv] at h1
    exact (mem_normalizer_iff.1 (hYZ hy) _).1 h1
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime (N := N)
    (fun x hx => hx.1) (fun x hx => mem_normalizer_of_conj_mem fun z hz =>
      Common.conj_mem_centralizerMod hx hz) hAP (fun j hj => mem_normalizer_of_conj_mem
      fun z hz => ⟨(mem_normalizer_iff.1 (hAP hj) z).1 hz.1, fun y hy => by
        have hy' : j⁻¹ * y * j ∈ Y := by
          have := (mem_normalizer_iff.1 (inv_mem (hAY hj)) y).1 hy
          rwa [inv_inv] at this
        have h1 := (mem_normalizer_iff.1 (hAZ hj) _).1 (hz.2 _ hy')
        rwa [show j * (z * (j⁻¹ * y * j) * z⁻¹ * (j⁻¹ * y * j)⁻¹) * j⁻¹ =
          j * z * j⁻¹ * y * (j * z * j⁻¹)⁻¹ * y⁻¹ by group] at h1⟩)
    hsolv hcop hx hfix
  rw [show c * n * y * (c * n)⁻¹ * y⁻¹ = c * (n * y * n⁻¹ * y⁻¹) * c⁻¹ * (c * y * c⁻¹ * y⁻¹) by
    group]
  exact mul_mem (hB c hc.1 _ (hn.2 y hy)) (hC c hc y hy)

theorem mem_of_map_upperCentralSeries_succ {P Z Z' : Subgroup G} {n : ℕ}
    (hZ : (Subgroup.upperCentralSeries P n).map P.subtype = Z)
    (hZ' : (Subgroup.upperCentralSeries P (n + 1)).map P.subtype = Z') {x : G} :
    x ∈ Z' ↔ x ∈ P ∧ ∀ g ∈ P, x * g * x⁻¹ * g⁻¹ ∈ Z := by
  have hmem : ∀ y : P, y ∈ Subgroup.upperCentralSeries P n ↔ (y : G) ∈ Z := fun y => by
    rw [← hZ]
    exact (mem_map_iff_mem P.subtype_injective).symm
  rw [← hZ']
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_upperCentralSeries_succ_iff] at hy
    refine ⟨y.2, fun g hg => ?_⟩
    have := (hmem _).1 (hy ⟨g, hg⟩)
    simpa [commutatorElement_def] using this
  · rintro ⟨hxP, hx⟩
    refine ⟨⟨x, hxP⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_upperCentralSeries_succ_iff]
    intro g
    rw [hmem]
    simpa [commutatorElement_def] using hx g g.2

theorem le_of_index_two_of_fixed_le {C₀ A B D₁ J : Subgroup G} {t : G}
    (ht2 : t * t = 1) (hAC : A ⊔ zpowers t = C₀) (hBC : B ⊔ zpowers t = C₀)
    (htA : t ∈ normalizer (A : Set G)) (htB : t ∈ normalizer (B : Set G)) (htA' : t ∉ A)
    (hD₁A : D₁ ≤ A) (hD₁B : D₁ ≤ B) (hJt : ∀ j ∈ J, j * t = t * j)
    (hJC₀ : J ≤ normalizer (C₀ : Set G)) (hJA : J ≤ normalizer (A : Set G))
    (hJB : J ≤ normalizer (B : Set G)) (hsolv : Group.IsSolvable C₀)
    (hcop : (Nat.card J).Coprime (Nat.card C₀))
    (hfpf : ∀ c ∈ C₀ ⊓ centralizer (J : Set G), c ∈ D₁ ∨ ∃ d ∈ D₁, c = d * t) : A ≤ B := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  intro a ha
  have hC₀A : C₀ ≤ normalizer (A : Set G) :=
    hAC ▸ sup_le le_normalizer ((zpowers_le).2 htA)
  have hC₀B : C₀ ≤ normalizer (B : Set G) :=
    hBC ▸ sup_le le_normalizer ((zpowers_le).2 htB)
  have haC₀ : a ∈ C₀ := hAC ▸ mem_sup_left ha
  have hNC₀ : A ⊓ B ≤ C₀ := inf_le_left.trans (hAC ▸ le_sup_left)
  have hC₀N : C₀ ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := fun g hg =>
    Common.mem_normalizer_inf (hC₀A hg) (hC₀B hg)
  have hJN : J ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := fun j hj =>
    Common.mem_normalizer_inf (hJA hj) (hJB hj)
  have hfix : ∀ j ∈ J, a⁻¹ * (j * a * j⁻¹) ∈ A ⊓ B := by
    intro j hj
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha) ((mem_normalizer_iff.1 (hJA hj) a).1 ha), ?_⟩
    have haB : a ∈ B ⊔ zpowers t := hBC ▸ haC₀
    rcases (mem_sup_zpowers_iff_of ht2 htB).1 haB with hb | ⟨b, hb, rfl⟩
    · exact mul_mem (inv_mem hb) ((mem_normalizer_iff.1 (hJB hj) a).1 hb)
    · have hjtj : j * t * j⁻¹ = t := by rw [hJt j hj]; group
      have e : (b * t)⁻¹ * (j * (b * t) * j⁻¹) = t * (b⁻¹ * (j * b * j⁻¹)) * t := by
        have : (b * t)⁻¹ * (j * (b * t) * j⁻¹) =
            t⁻¹ * (b⁻¹ * (j * b * j⁻¹)) * (j * t * j⁻¹) := by group
        rw [this, hjtj, htinv]
      rw [e]
      have hx : b⁻¹ * (j * b * j⁻¹) ∈ B :=
        mul_mem (inv_mem hb) ((mem_normalizer_iff.1 (hJB hj) b).1 hb)
      have := (mem_normalizer_iff.1 htB _).1 hx
      rwa [htinv] at this
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime hNC₀ hC₀N hJC₀
    hJN hsolv hcop haC₀ hfix
  have hcA : c ∈ A := by
    have := mul_mem ha (inv_mem hn.1)
    rwa [mul_inv_cancel_right] at this
  rcases hfpf c hc with hcD | ⟨d, hd, hcd⟩
  · exact mul_mem (hD₁B hcD) hn.2
  · exfalso
    refine htA' ?_
    have := mul_mem (inv_mem (hD₁A hd)) hcA
    rwa [hcd, inv_mul_cancel_left] at this

theorem mem_normalizer_map_conj {A : Subgroup G} {w g : G} (hg : g ∈ normalizer (A : Set G)) :
    w * g * w⁻¹ ∈ normalizer ((A.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_map_conj_iff, mem_map_conj_iff,
    show w⁻¹ * ((w * g * w⁻¹) * x * (w * g * w⁻¹)⁻¹) * w = g * (w⁻¹ * x * w) * g⁻¹ by group]
  exact mem_normalizer_iff.1 hg _

end Generic

end Q52

namespace Model

namespace Q52

variable
  {K : Type} [Field K] [CharP K 2]

theorem W_inf_map_wa_W_le : W K ⊓ (W K).map (MulAut.conj (wa K)).toMonoidHom ≤ U K := by
  rintro x ⟨hxW, hxW'⟩
  obtain ⟨D, E, F, rfl⟩ := mem_W.1 hxW
  obtain ⟨_, ⟨D', E', F', rfl⟩, he⟩ := hxW'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, wa] at he
  have h1 : weylElt .G2 K g2ir 1 * g2N 0 0 0 D' E' F' * (weylElt .G2 K g2ir 1)⁻¹ =
      g2N 0 E' D' 0 0 F' := by
    rw [show g2N 0 0 0 D' E' F' = g2N 0 0 0 D' E' F' from rfl, weylElt_r_conj_g2N]
    refine g2N_eq_g2N rfl rfl rfl rfl rfl ?_
    ring
  rw [h1] at he
  obtain ⟨-, -, -, hD, hE, -⟩ := g2N_injective he
  exact mem_U.2 ⟨F, by rw [← hD, ← hE]⟩

end Q52

end Model

namespace G2Data

namespace Q52

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

variable
  [CharP K 2]

theorem W_inf_map_wa_le_U :
    d.W ⊓ d.W.map (MulAut.conj d.wa).toMonoidHom ≤ d.U := by
  have h2 : d.W ⊓ d.W.map (MulAut.conj d.wa).toMonoidHom =
      d.image (Model.W K ⊓ (Model.W K).map (MulAut.conj (Model.wa K)).toMonoidHom) := by
    rw [d.image_inf, d.image_conj.1]
    rfl
  rw [h2]
  exact d.image_mono Model.Q52.W_inf_map_wa_W_le

theorem wa_mem_normalizer_J [Finite K] (hK : 4 ≤ Nat.card K) :
    d.wa ∈ normalizer (d.J : Set G) := by
  have h37 := d.yamada_3_7_G hK
  have : d.wa ∈ L ⊓ normalizer (d.J : Set G) := by
    rw [h37.1]
    exact mem_sup_right (subset_closure (Set.mem_insert _ _))
  exact this.2

end Q52

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

namespace Q52

theorem yamadaR₈_le_normalizer_yamadaS₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₈ d t ≤ normalizer (yamadaS₅ d t : Set G) := by
  obtain ⟨⟨-, -, -, hS₅R₅⟩, -, -, -, hS₅c⟩ := h.yamada_5_46_4 hW d hK hQ
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((yamadaS₅ d t).subgroupOf (yamadaR₅ d t))
  rw [subgroupOf_map_subtype, inf_of_le_left hS₅R₅] at h1
  exact (yamadaR₈_le d t).trans h1

theorem yamadaR₈_le_normalizer_yamadaU₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₈ d t ≤ normalizer (yamadaU₁ d t : Set G) := by
  obtain ⟨⟨hZ, -⟩, -⟩ := h.yamada_5_45_1 hW d hK hQ
  rw [map_upperCentralSeries_one] at hZ
  rw [← hZ]
  exact (Q52.yamadaR₈_le_normalizer_yamadaS₅ hW h d hK hQ).trans (normalizer_le_normalizer_center _)

theorem yamadaR₈_le_normalizer_yamadaY₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₈ d t ≤ normalizer (yamadaY₂ d t : Set G) := by
  obtain ⟨⟨hZ, -⟩, ⟨hZ2, -⟩⟩ := h.yamada_5_45_1 hW d hK hQ
  have hS := Q52.yamadaR₈_le_normalizer_yamadaS₅ hW h d hK hQ
  have hU := Q52.yamadaR₈_le_normalizer_yamadaU₁ hW h d hK hQ
  intro g hg
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  rw [Q52.mem_of_map_upperCentralSeries_succ hZ hZ2] at hy ⊢
  obtain ⟨hyS, hy⟩ := hy
  refine ⟨(mem_normalizer_iff.1 (hS hg) y).1 hyS, fun s hs => ?_⟩
  have hs' : g⁻¹ * s * g ∈ yamadaS₅ d t := by
    have := (mem_normalizer_iff.1 (inv_mem (hS hg)) s).1 hs
    rwa [inv_inv] at this
  have := (mem_normalizer_iff.1 (hU hg) _).1 (hy _ hs')
  rwa [show g * (y * (g⁻¹ * s * g) * y⁻¹ * (g⁻¹ * s * g)⁻¹) * g⁻¹ =
    g * y * g⁻¹ * s * (g * y * g⁻¹)⁻¹ * s⁻¹ by group] at this

theorem yamadaP_inf_centralizer_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {A : Subgroup G}
    (hAJ : A ≤ d.J) (hAF : d.S ⊓ centralizer (A : Set G) ≤ d.F) :
    yamadaP d t ⊓ centralizer (A : Set G) ≤ yamadaS₅ d t := by
  have hD := hQ.doubling
  obtain ⟨-, hPR₈, -, -, -, hPR₅, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨hR₅n, hFSn, φ, -, hφ⟩ := h.yamada_5_49_3 hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hFS : d.F ≤ d.S := hFD.trans hDS
  have hSF : d.S ≤ normalizer (d.F : Set G) := (normal_subgroupOf_iff_le_normalizer hFS).1 hFSn
  have hJS := h.J_le_centralizer_inf_normalizer_S d
  have hJF := h.centralizer_inf_normalizer_S_le_normalizer_F d hK hD
  intro c hc
  obtain ⟨hcP, hcA⟩ := Subgroup.mem_inf.1 hc
  set x : yamadaR₈ d t := ⟨c, hPR₈ hcP⟩ with hx
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (φ (QuotientGroup.mk x))
  have hfix : ∀ a ∈ A, (s : G)⁻¹ * (a * s * a⁻¹) ∈ d.F := by
    intro a ha
    obtain ⟨hxa, hsa, he⟩ := hφ a (hJS (hAJ ha)) x s hs.symm
    have hac : a * c * a⁻¹ = c := by
      have := mem_centralizer_iff.1 hcA a ha
      rw [this, mul_inv_cancel_right]
    have hxx : (⟨a * x * a⁻¹, hxa⟩ : yamadaR₈ d t) = x := Subtype.ext hac
    rw [hxx, ← hs] at he
    have := QuotientGroup.eq.1 he
    rwa [mem_subgroupOf] at this
  have hsolv : Group.IsSolvable d.S := by
    have := d.isSylowOf_S.isPGroup.isNilpotent
    infer_instance
  have hAS : A ≤ normalizer (d.S : Set G) := fun a ha => (Subgroup.mem_inf.1 (hJS (hAJ ha))).2
  have hAF' : A ≤ normalizer (d.F : Set G) := fun a ha => hJF (hJS (hAJ ha))
  have hcop : (Nat.card A).Coprime (Nat.card d.S) := by
    have := coprime_card_J d d.isSylowOf_S.isPGroup
    exact Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hAJ) this
  obtain ⟨c', hc', n, hn, hsn⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime (N := d.F)
    hFS hSF hAS hAF' hsolv hcop s.2 hfix
  have hsF : (s : G) ∈ d.F := by
    rw [hsn]
    exact mul_mem (hAF hc') hn
  have h1 : (QuotientGroup.mk s : d.S ⧸ d.F.subgroupOf d.S) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hsF)
  rw [h1, ← MulEquiv.map_one φ] at hs
  have h2 := φ.injective hs.symm
  have h3 := (QuotientGroup.eq_one_iff _).1 h2
  rw [mem_subgroupOf] at h3
  rw [← hPR₅]
  exact ⟨hcP, h3⟩

theorem isPGroup_yamadaR₈ (d : G2Data L K) (t : G) : IsPGroup 2 (yamadaR₈ d t) :=
  LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem J₁_sup_J₃ (d : G2Data L K) : d.J₁ ⊔ d.J₃ = d.J := by
  have hJ₁J : d.J₁ ≤ d.J := d.image_mono inf_le_left
  have hJ₃J : d.J₃ ≤ d.J := d.image_mono inf_le_left
  have hm : Model.J₁ K ⊓ Model.J₃ K = ⊥ :=
    Model.Ji_inf_Ji_eq_bot (K := K) (i := 0) (k := 2) (by decide) (Or.inr (by decide))
  have hinf : d.J₁ ⊓ d.J₃ = ⊥ := by
    rw [G2Data.J₁, G2Data.J₃, ← d.image_inf, hm, d.image_bot]
  have hc : Nat.card d.J = (Nat.card K - 1) ^ 2 := by
    rw [Nat.card_congr d.torusChars.toEquiv, Nat.card_prod, Nat.card_units, sq]
  have hN : d.J₃ ≤ normalizer (d.J₁ : Set G) := fun j hj =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => d.J₁_comm_J₃ hx hj)
  have h1 := Common.card_sup_mul_card_inf_eq (A := d.J₁) (B := d.J₃) hN
  rw [hinf, Subgroup.card_bot, mul_one, d.card_J₁, d.card_J₃, ← sq] at h1
  exact Subgroup.eq_of_le_of_card_ge (sup_le hJ₁J hJ₃J) (hc.le.trans h1.ge)

end Q52

theorem yamada_5_52 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (Subgroup.upperCentralSeries (yamadaP d t) 1).map (yamadaP d t).subtype = yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaP d t) 2).map (yamadaP d t).subtype =
        yamadaY₂ d t := by
  have hD := hQ.doubling
  obtain ⟨hJR₈, hPR₈, -, hS₅S₆, hS₆P, hPR₅, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨-, hR₈S₂⟩ := h.normalizer_inf_yamadaR₈ hW d hK hQ
  obtain ⟨⟨hZ, -⟩, ⟨hZ2, -⟩⟩ := h.yamada_5_45_1 hW d hK hQ
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hS₅P : yamadaS₅ d t ≤ yamadaP d t := hS₅S₆.trans hS₆P
  have hS₂S₅ : yamadaS₂ d t ≤ yamadaS₅ d t :=
    (le_sup_right : yamadaS₂ d t ≤ yamadaS₃ d t).trans le_sup_left
  have hS₂P : yamadaS₂ d t ≤ yamadaP d t := hS₂S₅.trans hS₅P
  have hU₁S₂ : yamadaU₁ d t ≤ yamadaS₂ d t := (yamadaU₁_le_yamadaY₂ d t).trans le_sup_right
  have hY₂S₂ : yamadaY₂ d t ≤ yamadaS₂ d t := le_sup_right
  have hU₁S₅ : yamadaU₁ d t ≤ yamadaS₅ d t := hU₁S₂.trans hS₂S₅
  have hZ' : yamadaS₅ d t ⊓ centralizer (yamadaS₅ d t : Set G) = yamadaU₁ d t := by
    rw [← map_upperCentralSeries_one]
    exact hZ
  have hmemY₂ : ∀ x, x ∈ yamadaY₂ d t ↔
      x ∈ yamadaS₅ d t ∧ ∀ g ∈ yamadaS₅ d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaU₁ d t := fun x =>
    Q52.mem_of_map_upperCentralSeries_succ hZ hZ2
  have hU₁c : ∀ u ∈ yamadaU₁ d t, ∀ g ∈ yamadaS₅ d t, g * u = u * g := fun u hu g hg => by
    have : u ∈ yamadaS₅ d t ⊓ centralizer (yamadaS₅ d t : Set G) := by
      rw [hZ']
      exact hu
    exact mem_centralizer_iff.1 this.2 g hg
  have hPS₅ : yamadaP d t ≤ normalizer (yamadaS₅ d t : Set G) :=
    hPR₈.trans (Q52.yamadaR₈_le_normalizer_yamadaS₅ hW h d hK hQ)
  have hPU₁ : yamadaP d t ≤ normalizer (yamadaU₁ d t : Set G) :=
    hPR₈.trans (Q52.yamadaR₈_le_normalizer_yamadaU₁ hW h d hK hQ)
  have hPY₂ : yamadaP d t ≤ normalizer (yamadaY₂ d t : Set G) :=
    hPR₈.trans (Q52.yamadaR₈_le_normalizer_yamadaY₂ hW h d hK hQ)
  have hP2 : IsPGroup 2 (yamadaP d t) := (Q52.isPGroup_yamadaR₈ d t).to_le hPR₈
  have hsolv : Group.IsSolvable (yamadaP d t) := by
    have := hP2.isNilpotent
    infer_instance
  have hJP : d.J ≤ normalizer (yamadaP d t : Set G) := fun j hj =>
    mem_normalizer_commutator (hJR₈ hj) (Subgroup.le_normalizer hj)
  have hbot : ∀ g : G, g ∈ normalizer ((⊥ : Subgroup G) : Set G) := fun g => by
    rw [mem_normalizer_iff]
    intro n
    simp only [SetLike.mem_coe, Subgroup.mem_bot, mul_inv_eq_one, mul_eq_one_iff_eq_inv]
    constructor
    · intro hn
      simp [hn]
    · intro hn
      simpa using hn
  have hJ₁J : d.J₁ ≤ d.J := d.image_mono inf_le_left
  have hJ₃J : d.J₃ ≤ d.J := d.image_mono inf_le_left
  have hJ₅J : d.J₅ ≤ d.J := d.J₅_le_J
  have hq : (yamadaP d t ⊓ centralizer (d.J₁ : Set G) ≤ centralizer (yamadaU₁ d t : Set G)) ∧
      ∀ c ∈ yamadaP d t ⊓ centralizer (d.J₅ : Set G), ∀ y ∈ yamadaY₂ d t,
        c * y * c⁻¹ * y⁻¹ ∈ yamadaU₁ d t := by
    rcases hQ.branch with h8 | ⟨hK4, hQ4⟩
    · refine ⟨fun c hc => ?_, fun c hc y hy => ?_⟩
      · have hcS₅ := Q52.yamadaP_inf_centralizer_le hW h d hK hQ hJ₁J
          (by rw [d.S_inf_centralizer_J₁ h8]; exact hUY.trans (hYX.trans hXF)) hc
        exact mem_centralizer_iff.2 fun u hu => (hU₁c u hu c hcS₅).symm
      · have hcS₅ := Q52.yamadaP_inf_centralizer_le hW h d hK hQ hJ₅J (by
          rw [d.S_inf_centralizer_J₅ h8]
          exact (le_sup_left.trans (d.yamada_defs).1.le).trans (hYX.trans hXF)) hc
        have h1 := ((hmemY₂ y).1 hy).2 c hcS₅
        have := inv_mem h1
        rwa [show (y * c * y⁻¹ * c⁻¹)⁻¹ = c * y * c⁻¹ * y⁻¹ by group] at this
    ·
      have hJ₁₅ : d.J₁ = d.J₅ := (d.yamada_3_9_4_four_G hK4).2.1
      have hD₁P : yamadaD₁ d t ≤ yamadaP d t := by
        rw [hD.D₁_eq]
        exact sup_le (hDS.trans ((le_sup_left : d.S ≤ yamadaS₂ d t).trans hS₂P))
          (hU₁S₂.trans hS₂P)
      set A : Subgroup G := yamadaP d t ⊓ centralizer (d.J₁ : Set G) with hAdef
      have hA2 : IsPGroup 2 A := hP2.to_le inf_le_left
      have hXA : yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ A := fun x hx => ⟨hD₁P hx.1, hx.2⟩
      have hAB : A ≤ yamadaB d := by
        refine h.le_yamadaB_of_four d hK hA2 inf_le_right (fun j hj => ?_) (fun x hx => ?_)
        · exact Common.mem_normalizer_inf (hJP (hJ₃J hj))
            (mem_normalizer_centralizer_of_mem_normalizer (Subgroup.centralizer_le_normalizer _
              (mem_centralizer_iff.2 fun j' hj' => d.J₁_comm_J₃ hj' hj)))
        ·
          obtain ⟨⟨hxP, hxJ₁⟩, hxJ₃⟩ := hx
          have hxJ : x ∈ centralizer (d.J : Set G) := by
            have hle : d.J ≤ centralizer ({x} : Set G) := by
              rw [← Q52.J₁_sup_J₃ d]
              exact sup_le
                (fun j hj => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxJ₁ j hj))
                (fun j hj => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxJ₃ j hj))
            exact mem_centralizer_iff.2 fun j hj => mem_centralizer_singleton_iff.1 (hle hj)
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
            (q49_yamadaR₈_inf_centralizer_J_le hW h d hK hQ ⟨hPR₈ hxP, hxJ⟩)
          obtain ⟨⟨-, -, htP⟩, -⟩ := h.yamada_5_51 hW d hK hQ
          rcases h.zpow_eq_one_or_eq k with hk1 | hk1
          · rw [hk1] at hk
            rw [← hk]
            exact one_mem _
          · rw [hk1] at hk
            exact absurd (hk ▸ hxP) htP
      refine ⟨hQ4.le_centralizer_U₁ hAB hA2 hXA, fun c hc y hy => ?_⟩
      rw [← hJ₁₅] at hc
      have hyA : y ∈ A := ⟨(hY₂S₂.trans hS₂P) hy, h.yamadaY₂_le_centralizer_J₁_four d hD hK4 hy⟩
      rcases hD.branch with h8 | ⟨-, -, -, hE⟩
      · omega
      · exact (hE A hAB hA2 hXA c hc y hyA).2
  have hZP : yamadaP d t ⊓ centralizer (yamadaP d t : Set G) ≤ yamadaU₁ d t := by
    rintro x ⟨hxP, hxc⟩
    have hxS₂ : x ∈ normalizer (yamadaS₂ d t : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hS₂P hxc)
    have hxR₅ : x ∈ yamadaR₅ d t := by
      rw [← hR₈S₂]
      exact ⟨hPR₈ hxP, hxS₂⟩
    have hxS₅ : x ∈ yamadaS₅ d t := by
      rw [← hPR₅]
      exact ⟨hxP, hxR₅⟩
    rw [← hZ']
    exact ⟨hxS₅, Subgroup.centralizer_le hS₅P hxc⟩
  have hU₁Z : yamadaU₁ d t ≤ yamadaP d t ⊓ centralizer (yamadaP d t : Set G) := by
    have hcop : (Nat.card d.J₁).Coprime (Nat.card (yamadaP d t)) :=
      Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hJ₁J) (coprime_card_J d hP2)
    have key := Q52.commutator_mem_of_coprime_trivial (P := yamadaP d t) (A := d.J₁)
      (Y := yamadaU₁ d t) (Z := ⊥) hsolv hcop (fun j hj => hJP (hJ₁J hj))
      (fun j hj => h.J_le_normalizer_yamadaU₁ d hK hD (hJ₁J hj)) (fun j _ => hbot j) hPU₁
      (fun g _ => hbot g) (fun y _ => hbot y)
      (fun a ha y hy => by
        have := mem_centralizer_iff.1 (hD.le_centralizer_J₁ hy) a ha
        rw [this, mul_inv_cancel_right, inv_mul_cancel]
        exact one_mem _)
      (fun c hc y hy => by
        have := (mem_centralizer_iff.1 (hq.1 hc) y hy).symm
        rw [this, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _)
    intro u hu
    refine ⟨hU₁S₅ hu |> hS₅P, mem_centralizer_iff.2 fun g hg => ?_⟩
    have := key g hg u hu
    rw [Subgroup.mem_bot] at this
    calc g * u = (g * u * g⁻¹ * u⁻¹) * (u * g) := by group
      _ = u * g := by rw [this, one_mul]
  have hfirst : (Subgroup.upperCentralSeries (yamadaP d t) 1).map (yamadaP d t).subtype =
      yamadaU₁ d t := by
    rw [map_upperCentralSeries_one]
    exact le_antisymm hZP hU₁Z
  have hP_Y₂ : ∀ x ∈ yamadaP d t, ∀ y ∈ yamadaY₂ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaU₁ d t := by
    have hcop : (Nat.card d.J₅).Coprime (Nat.card (yamadaP d t)) :=
      Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hJ₅J) (coprime_card_J d hP2)
    have hJ₅U₁ : d.J₅ ≤ normalizer (yamadaU₁ d t : Set G) := fun j hj =>
      h.J_le_normalizer_yamadaU₁ d hK hD (hJ₅J hj)
    refine Q52.commutator_mem_of_coprime_trivial (P := yamadaP d t) (A := d.J₅)
      (Y := yamadaY₂ d t) (Z := yamadaU₁ d t) hsolv hcop (fun j hj => hJP (hJ₅J hj))
      (fun j hj => mem_normalizer_sup (hJ₅U₁ hj)
        (Subgroup.centralizer_le_normalizer _ (h.J₅_le_centralizer_map_wb d hD hj)))
      hJ₅U₁ hPY₂ hPU₁ (h.yamadaY₂_le_normalizer_yamadaU₁ d hK hD)
      (fun a ha y hy => h.mul_conj_mem_yamadaU₁_of_mem_J₅ d hK hD ha hy)
      (fun c hc y hy => hq.2 c hc y hy)
  refine ⟨hfirst, map_upperCentralSeries_succ (n := 1) hfirst (hY₂S₂.trans hS₂P) fun x hx => ?_⟩
  constructor
  · intro hxY g hg
    have := inv_mem (hP_Y₂ g hg x hxY)
    rwa [show (g * x * g⁻¹ * x⁻¹)⁻¹ = x * g * x⁻¹ * g⁻¹ by group] at this
  · intro hxZ
    have hxN : x ∈ normalizer (yamadaS₂ d t : Set G) := by
      refine mem_normalizer_of_conj_mem fun s hs => ?_
      have h1 := hxZ s (hS₂P hs)
      have h2 := mul_mem (hU₁S₂ h1) hs
      rwa [show x * s * x⁻¹ * s⁻¹ * s = x * s * x⁻¹ by group] at h2
    have hxR₅ : x ∈ yamadaR₅ d t := by
      rw [← hR₈S₂]
      exact ⟨hPR₈ hx, hxN⟩
    have hxS₅ : x ∈ yamadaS₅ d t := by
      rw [← hPR₅]
      exact ⟨hx, hxR₅⟩
    exact (hmemY₂ x).2 ⟨hxS₅, fun g hg => hxZ g (hS₅P hg)⟩

namespace Q52

theorem yamadaC₁_le_yamadaCstar (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaC₁ d t ≤ yamadaCstar d t := by
  obtain ⟨⟨-, -, hC₁inf⟩, -⟩ := h.yamada_5_19 d hK hD
  rw [← hC₁inf]
  exact inf_le_left

theorem inf_normalizer_U_le_normalizer_yamadaC₇ (h : Setup G L f t) (d : G2Data L K) :
    L ⊓ normalizer (d.U : Set G) ≤ normalizer (yamadaC₇ d t : Set G) := fun n hn =>
  LieType.BorelTits.le_normalizer_pCoreOf 2 _ (h.inf_normalizer_U_le_normalizer_yamadaC₁ d hn)

theorem mul_self_mem_yamadaC₁_of_mem_yamadaCstar (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G} (hg : g ∈ yamadaCstar d t) :
    g * g ∈ yamadaC₁ d t := by
  have hCV := h.yamadaCstar_eq d hK hD
  have hgV : g ∈ h.yamadaV d hK hD := hCV ▸ hg
  have hgN := ((h.mem_yamadaV d hK hD).1 hgV).1
  have h1 := h.crossed_mul_mem d hK hD hgV hgN
  obtain ⟨δ, hδ, hgt⟩ := h.exists_conj_t_eq d hK hD hgN
  have hκ : t * g * t * g⁻¹ = δ := by
    rw [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group, hgt, ← mul_assoc, h.t_mul_t, one_mul]
  have hδ2 : δ * δ ∈ yamadaU₁ d t := by
    have hsq : δ ^ 2 ∈ closure {z | ∃ g ∈ yamadaC₁ d t, z = g ^ 2} :=
      subset_closure ⟨δ, h.yamadaD₁_le_yamadaC₁ d hK hδ, rfl⟩
    rw [h.yamada_5_6_4 d hK] at hsq
    rw [← sq]
    exact hD.U_le hsq
  refine h.mem_yamadaC₁_of_crossed_mem d hK hD (mul_mem hgV hgV) ?_
  rw [hκ] at h1
  have := mul_mem hδ2 h1
  rwa [mul_inv_cancel_left] at this

theorem yamadaD₁_le_yamadaS₂ (h : Setup G L f t) (d : G2Data L K) (hD : h.DoublingFacts d) :
    yamadaD₁ d t ≤ yamadaS₂ d t := by
  obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
  rw [hD.D₁_eq]
  exact sup_le (hDS.trans le_sup_left) ((yamadaU₁_le_yamadaY₂ d t).trans le_sup_right)

theorem yamadaD₁_le_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaD₁ d t ≤ yamadaD₇ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, hS₅S₆, hS₆P, -, -⟩ := h.yamadaP_facts hW d hK hQ
  have hS₂S₅ : yamadaS₂ d t ≤ yamadaS₅ d t :=
    (le_sup_right : yamadaS₂ d t ≤ yamadaS₃ d t).trans le_sup_left
  exact le_inf (((Q52.yamadaD₁_le_yamadaS₂ h d hD).trans hS₂S₅).trans (hS₅S₆.trans hS₆P))
    ((h.yamadaD₁_le_yamadaC₁ d hK).trans (Q52.yamadaC₁_le_yamadaCstar h d hK hD))

theorem yamadaC₁_inf_yamadaD₇_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaC₁ d t ⊓ yamadaD₇ d t ≤ yamadaD₁ d t := by
  obtain ⟨-, -, -, -, htD₇⟩ := h.yamada_5_51 hW d hK hQ
  obtain ⟨-, hC₁eq, -⟩ := h.yamada_5_8_1 d hK
  have hD₁D₇ := Q52.yamadaD₁_le_yamadaD₇ hW h d hK hQ
  intro x hx
  obtain ⟨hxC₁, hxD₇⟩ := Subgroup.mem_inf.1 hx
  have h3 : x ∈ yamadaD₁ d t ⊔ zpowers t := hC₁eq ▸ hxC₁
  rcases (mem_sup_zpowers_iff_of h.t_mul_t (h.yamadaC₁_le_normalizer_yamadaD₁ d hK
    (h.t_mem_yamadaC₁ d hK))).1 h3 with h4 | ⟨a, ha, he⟩
  · exact h4
  · exfalso
    refine htD₇ ?_
    have h5 := mul_mem (inv_mem (hD₁D₇ ha)) hxD₇
    rwa [he, inv_mul_cancel_left] at h5

end Q52

theorem yamada_5_53 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    closure {z | ∃ g ∈ yamadaC₇ d t, z = g ^ 2} = yamadaD₁ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, hD₇C, htD₇N, htD₇⟩ := h.yamada_5_51 hW d hK hQ
  obtain ⟨-, -, -, -, hC₂eq, -⟩ := h.yamada_5_19 d hK hD
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -, -, -, -⟩ := d.inclusions
  apply le_antisymm
  · rw [closure_le]
    rintro z ⟨g, hg, rfl⟩
    have hgC : g ∈ yamadaCstar d t := hg
    refine Q52.yamadaC₁_inf_yamadaD₇_le hW h d hK hQ ⟨?_, ?_⟩
    · rw [sq]
      exact Q52.mul_self_mem_yamadaC₁_of_mem_yamadaCstar h d hK hD hgC
    · rw [sq]
      have hgs : g ∈ yamadaD₇ d t ⊔ zpowers t := hD₇C ▸ hgC
      rcases (mem_sup_zpowers_iff_of h.t_mul_t htD₇N).1 hgs with h3 | ⟨a, ha, rfl⟩
      · exact mul_mem h3 h3
      · have := (mem_normalizer_iff.1 htD₇N a).1 ha
        rw [show a * t * (a * t) = a * (t * a * t⁻¹) by
          rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right h.t_mul_t]; group]
        exact mul_mem ha this
  · set Kk := closure {z | ∃ g ∈ yamadaC₇ d t, z = g ^ 2} with hKk
    have hC₂C₇ : yamadaC₂ d t ≤ yamadaC₇ d t := hC₂eq.le.trans inf_le_left
    have hY₁K : yamadaY₁ d t ≤ Kk := by
      rw [← (h.yamada_5_15_3 d hK hD).2.2]
      exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, hC₂C₇ hg, e⟩
    have hU₁K : yamadaU₁ d t ≤ Kk := (le_sup_right : yamadaU₁ d t ≤ yamadaY₁ d t).trans hY₁K
    have hYK : d.Y ≤ Kk := (le_sup_left : d.Y ≤ yamadaY₁ d t).trans hY₁K
    have hNK : L ⊓ normalizer (d.U : Set G) ≤ normalizer (Kk : Set G) := fun n hn =>
      mem_normalizer_closure_sq_of_mem_normalizer
        (Q52.inf_normalizer_U_le_normalizer_yamadaC₇ h d hn)
    have hND : L ⊓ normalizer (d.U : Set G) ≤ normalizer (d.D : Set G) := fun n hn =>
      h.centralizer_inf_normalizer_U_le_normalizer_D d hK ⟨h.L_le_centralizer hn.1, hn.2⟩
    have hYD : d.Y ≤ d.D := hYX.trans (hXF.trans hFD)
    have hUK : d.U ≤ Kk ⊓ d.D := le_inf (hD.U_le.trans hU₁K) (hUY.trans hYD)
    have h4 : 4 ≤ Nat.card K := hQ.four_le
    rcases (d.yamada_3_16_1_G h4 hUK inf_le_right).1 (fun n hn =>
      Common.mem_normalizer_inf (hNK hn) (hND hn)) with he | he
    · exfalso
      have hYU : d.Y ≤ d.U := by
        rw [← he]
        exact le_inf hYK hYD
      have := Subgroup.card_le_of_le hYU
      rw [d.cards.2.1, d.cards.1] at this
      nlinarith
    · have hDK : d.D ≤ Kk := by
        rw [← he]
        exact inf_le_left
      rw [hD.D₁_eq]
      exact sup_le hDK hU₁K

namespace Q52

theorem yamadaCstar_inf_centralizer_le (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {A : Subgroup G} (hAL : A ≤ L)
    (hA : yamadaD₁ d t ⊓ centralizer (A : Set G) ≤ yamadaU₁ d t) :
    yamadaCstar d t ⊓ centralizer (A : Set G) ≤ yamadaC₁ d t := by
  have hCV := h.yamadaCstar_eq d hK hD
  intro c hc
  obtain ⟨hcC, hcJ⟩ := Subgroup.mem_inf.1 hc
  have hcV : c ∈ h.yamadaV d hK hD := hCV ▸ hcC
  have hcN := ((h.mem_yamadaV d hK hD).1 hcV).1
  obtain ⟨δ, hδ, hgt⟩ := h.exists_conj_t_eq d hK hD hcN
  have hκ : t * c * t * c⁻¹ = δ := by
    rw [show t * c * t * c⁻¹ = t * (c * t * c⁻¹) by group, hgt, ← mul_assoc, h.t_mul_t, one_mul]
  have hδJ : δ ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro j hj
    have hjc : j * c = c * j := mem_centralizer_iff.1 hcJ j hj
    have hjt : j * t = t * j := mem_centralizer_singleton_iff.1
      (h.L_le_centralizer (hAL hj))
    have hjcj : j * c * j⁻¹ = c := by rw [hjc, mul_inv_cancel_right]
    have hjtj : j * t * j⁻¹ = t := by rw [hjt, mul_inv_cancel_right]
    have e1 : j * (c * t * c⁻¹) * j⁻¹ = c * t * c⁻¹ := by
      calc j * (c * t * c⁻¹) * j⁻¹ = (j * c * j⁻¹) * (j * t * j⁻¹) * (j * c * j⁻¹)⁻¹ := by group
        _ = c * t * c⁻¹ := by rw [hjcj, hjtj]
    rw [hgt] at e1
    have e3 : t * (j * δ * j⁻¹) = t * δ := by
      calc t * (j * δ * j⁻¹) = (j * t * j⁻¹) * (j * δ * j⁻¹) := by rw [hjtj]
        _ = j * (t * δ) * j⁻¹ := by group
        _ = t * δ := e1
    have e4 := mul_left_cancel e3
    calc j * δ = (j * δ * j⁻¹) * j := by group
      _ = δ * j := by rw [e4]
  have hδU₁ : δ ∈ yamadaU₁ d t := hA (Subgroup.mem_inf.2 ⟨hδ, hδJ⟩)
  exact h.mem_yamadaC₁_of_crossed_mem d hK hD hcV (hκ ▸ hδU₁)

theorem yamadaCstar_inf_centralizer_J_le (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaCstar d t ⊓ centralizer (d.J : Set G) ≤ yamadaC₁ d t := by
  have hJ₁J : d.J₁ ≤ d.J := d.image_mono inf_le_left
  refine yamadaCstar_inf_centralizer_le h d hK hQ.doubling (d.image_le _) fun x hx => ?_
  rcases hQ.branch with h8 | ⟨hK4, -⟩
  · rw [yamadaU₁_eq d t h8]
    exact Subgroup.mem_inf.2 ⟨hx.1, Subgroup.centralizer_le hJ₁J hx.2⟩
  · have hJ₃J : d.J₃ ≤ d.J := d.image_mono inf_le_left
    have h1 := h.yamadaD₁_inf_centralizer_J₁_inf_centralizer_J₃ d hK hK4
    have h2 : x ∈ (⊥ : Subgroup G) := h1 ▸ Subgroup.mem_inf.2
      ⟨Subgroup.mem_inf.2 ⟨hx.1, Subgroup.centralizer_le hJ₁J hx.2⟩,
        Subgroup.centralizer_le hJ₃J hx.2⟩
    rw [Subgroup.mem_bot.1 h2]
    exact one_mem _

theorem wa_mem_normalizer_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.wa ∈ normalizer (yamadaD₇ d t : Set G) := by
  have hD := hQ.doubling
  have h4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨hJR₈, -, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨-, -, hC₇⟩ := h.yamada_5_51 hW d hK hQ
  obtain ⟨hD₇C, htN, htD₇⟩ := hC₇
  obtain ⟨hNU, hC₁eq, -⟩ := h.yamada_5_8_1 d hK
  have hwa := d.wa_mem_inf_normalizer_U
  have hwaN : d.wa ∈ normalizer (yamadaC₇ d t : Set G) :=
    Q52.inf_normalizer_U_le_normalizer_yamadaC₇ h d hwa
  have hwaD₁ : d.wa ∈ normalizer (yamadaD₁ d t : Set G) := hNU hwa
  have hwat : d.wa * t = t * d.wa :=
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer hwa.1)
  have hwaJ := G2Data.Q52.wa_mem_normalizer_J d h4
  have hconjt : d.wa * t * d.wa⁻¹ = t := by rw [hwat, mul_inv_cancel_right]
  have hconjt' : d.wa⁻¹ * t * d.wa = t := by rw [mul_assoc, ← hwat, inv_mul_cancel_left]
  have hD₁D₇ := Q52.yamadaD₁_le_yamadaD₇ hW h d hK hQ
  have hC₇2 : IsPGroup 2 (yamadaC₇ d t) := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hsolv : Group.IsSolvable (yamadaC₇ d t) := by
    have := hC₇2.isNilpotent
    infer_instance
  have hcop := coprime_card_J d hC₇2
  have hJC₇ : d.J ≤ normalizer (yamadaC₇ d t : Set G) := fun j hj =>
    Q52.inf_normalizer_U_le_normalizer_yamadaC₇ h d (d.J_le_inf_normalizer_U hj)
  have hJP : d.J ≤ normalizer (yamadaP d t : Set G) := fun j hj =>
    mem_normalizer_commutator (hJR₈ hj) (Subgroup.le_normalizer hj)
  have hJA : d.J ≤ normalizer (yamadaD₇ d t : Set G) := fun j hj =>
    Common.mem_normalizer_inf (hJP hj) (hJC₇ hj)
  have hJt : ∀ j ∈ d.J, j * t = t * j := fun j hj =>
    mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (h.J_le_centralizer_inf_normalizer_S d hj)).1
  have hJB : d.J ≤ normalizer ((yamadaD₇ d t).map (MulAut.conj d.wa).toMonoidHom : Set G) :=
    fun j hj => by
      have h1 : d.wa⁻¹ * j * d.wa ∈ d.J := by
        have := (mem_normalizer_iff.1 (inv_mem hwaJ) j).1 hj
        rwa [inv_inv] at this
      have := Q52.mem_normalizer_map_conj (w := d.wa) (hJA h1)
      rwa [show d.wa * (d.wa⁻¹ * j * d.wa) * d.wa⁻¹ = j by group] at this
  have hfpf : ∀ c ∈ yamadaC₇ d t ⊓ centralizer (d.J : Set G),
      c ∈ yamadaD₁ d t ∨ ∃ e ∈ yamadaD₁ d t, c = e * t := fun c hc => by
    have h1 : c ∈ yamadaC₁ d t := Q52.yamadaCstar_inf_centralizer_J_le h d hK hQ hc
    have h2 : c ∈ yamadaD₁ d t ⊔ zpowers t := hC₁eq ▸ h1
    exact (mem_sup_zpowers_iff_of h.t_mul_t
      (h.yamadaC₁_le_normalizer_yamadaD₁ d hK (h.t_mem_yamadaC₁ d hK))).1 h2
  have hBC : (yamadaD₇ d t).map (MulAut.conj d.wa).toMonoidHom ⊔ zpowers t = yamadaC₇ d t := by
    have h1 : ((yamadaD₇ d t) ⊔ zpowers t).map (MulAut.conj d.wa).toMonoidHom = yamadaC₇ d t := by
      rw [hD₇C]
      exact map_conj_eq_of_mem_normalizer hwaN
    rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h1
    have e : (MulAut.conj d.wa).toMonoidHom t = t := hconjt
    rwa [e] at h1
  have htB : t ∈ normalizer ((yamadaD₇ d t).map (MulAut.conj d.wa).toMonoidHom : Set G) := by
    have := Q52.mem_normalizer_map_conj (w := d.wa) htN
    rwa [hconjt] at this
  have htB' : t ∉ (yamadaD₇ d t).map (MulAut.conj d.wa).toMonoidHom := fun ht => by
    rw [mem_map_conj_iff, hconjt'] at ht
    exact htD₇ ht
  have hD₁B : yamadaD₁ d t ≤ (yamadaD₇ d t).map (MulAut.conj d.wa).toMonoidHom := fun x hx => by
    rw [mem_map_conj_iff]
    refine hD₁D₇ ?_
    have := (mem_normalizer_iff.1 (inv_mem hwaD₁) x).1 hx
    rwa [inv_inv] at this
  have hAB : yamadaD₇ d t ≤ (yamadaD₇ d t).map (MulAut.conj d.wa).toMonoidHom :=
    Q52.le_of_index_two_of_fixed_le (C₀ := yamadaC₇ d t) h.t_mul_t hD₇C hBC htN htB htD₇ hD₁D₇ hD₁B
      hJt hJC₇ hJA hJB hsolv hcop hfpf
  have hBA : (yamadaD₇ d t).map (MulAut.conj d.wa).toMonoidHom ≤ yamadaD₇ d t :=
    Q52.le_of_index_two_of_fixed_le (C₀ := yamadaC₇ d t) h.t_mul_t hBC hD₇C htB htN htB' hD₁B hD₁D₇
      hJt hJC₇ hJB hJA hsolv hcop hfpf
  exact mem_normalizer_of_map_conj_eq (le_antisymm hBA hAB)

theorem yamadaU₁_le_yamadaW₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaU₁ d t ≤ yamadaW₃ d t :=
  (yamadaU₁_le_yamadaY₂ d t).trans ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t).trans
    (h.yamadaW₃_facts hW d hK hD).2.2.2.1)

theorem yamadaW₃_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaW₃ d t ≤ yamadaL₃ d t ∧ yamadaW₃ d t ≤ yamadaR₃ d t ∧ yamadaW₃ d t ≤ yamadaC₃ d t ∧
      yamadaW₃ d t ≤ yamadaCstar d t := by
  have hWE : yamadaW₃ d t ≤ yamadaE₃ d t :=
    (h.yamadaW₃_facts hW d hK hD).1.trans (h.yamadaV₃_facts hW d hK hD).2.1
  have hEL : yamadaE₃ d t ≤ yamadaL₃ d t := inf_le_left
  have hEC : yamadaE₃ d t ≤ yamadaC₃ d t := inf_le_right
  have hCC : yamadaC₃ d t ≤ yamadaCstar d t := inf_le_right
  exact ⟨hWE.trans hEL, (hWE.trans hEL).trans le_sup_left, hWE.trans hEC,
    (hWE.trans hEC).trans hCC⟩

theorem crossed_mem_yamadaW₁_of_mem_yamadaW₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    {x : G} (hx : x ∈ yamadaW₃ d t) : t * x * t * x⁻¹ ∈ yamadaW₁ d t := by
  have hxR₃ : x ∈ yamadaR₃ d t := (Q52.yamadaW₃_le hW h d hK hD).2.1 hx
  have hxR₃' : x ∈ yamadaR₃star d t := (h.yamada_5_23_4 hW d hK hD) ▸ hxR₃
  exact ((h.mem_yamadaR₃star_iff d hK hD).1 hxR₃').2

theorem mem_yamadaU₁_of_mem_yamadaW₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaW₁ d t)
    (hx' : d.wa⁻¹ * x * d.wa ∈ yamadaW₁ d t) : x ∈ yamadaU₁ d t := by
  obtain ⟨hUY, -, hYW, -, hWF, hFD, -, -, -, -⟩ := d.inclusions
  have hWD : d.W ≤ d.D := hWF.trans hFD
  have hU₁W := h.yamadaU₁_le_normalizer_of_le_D d hK hD hWD
  have hwaU := d.wa_mem_inf_normalizer_U
  have hwaU₁ : d.wa ∈ normalizer (yamadaU₁ d t : Set G) :=
    hD.inf_normalizer_U_le_normalizer hK hwaU
  obtain ⟨w, hw, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer hU₁W x hx
  obtain ⟨w', hw', u', hu', hxe⟩ := Common.exists_mul_of_le_normalizer hU₁W _ hx'
  have hu''U₁ : d.wa * u' * d.wa⁻¹ ∈ yamadaU₁ d t := (mem_normalizer_iff.1 hwaU₁ u').1 hu'
  have hwu : w * u = (d.wa * w' * d.wa⁻¹) * (d.wa * u' * d.wa⁻¹) := by
    calc w * u = d.wa * (d.wa⁻¹ * (w * u) * d.wa) * d.wa⁻¹ := by group
      _ = d.wa * (w' * u') * d.wa⁻¹ := by rw [hxe]
      _ = (d.wa * w' * d.wa⁻¹) * (d.wa * u' * d.wa⁻¹) := by group
  have hvW : d.wa * w' * d.wa⁻¹ ∈ d.W.map (MulAut.conj d.wa).toMonoidHom := ⟨w', hw', rfl⟩
  have hvD : d.wa * w' * d.wa⁻¹ ∈ d.D := d.D_eq_W_sup_map_wa.2 hvW
  have hvw : (d.wa * w' * d.wa⁻¹)⁻¹ * w ∈ yamadaU₁ d t := by
    have : (d.wa * w' * d.wa⁻¹)⁻¹ * w = (d.wa * u' * d.wa⁻¹) * u⁻¹ := by
      calc (d.wa * w' * d.wa⁻¹)⁻¹ * w = (d.wa * w' * d.wa⁻¹)⁻¹ * (w * u) * u⁻¹ := by group
        _ = (d.wa * w' * d.wa⁻¹)⁻¹ * ((d.wa * w' * d.wa⁻¹) * (d.wa * u' * d.wa⁻¹)) * u⁻¹ := by
          rw [hwu]
        _ = (d.wa * u' * d.wa⁻¹) * u⁻¹ := by group
    rw [this]
    exact mul_mem hu''U₁ (inv_mem hu)
  have hvwU : (d.wa * w' * d.wa⁻¹)⁻¹ * w ∈ d.U := by
    rw [← hD.inf_D]
    exact Subgroup.mem_inf.2 ⟨hvw, mul_mem (inv_mem hvD) (hWD hw)⟩
  have hwW' : w ∈ d.W.map (MulAut.conj d.wa).toMonoidHom := by
    rw [show w = (d.wa * w' * d.wa⁻¹) * ((d.wa * w' * d.wa⁻¹)⁻¹ * w) by group]
    refine mul_mem hvW ?_
    rw [mem_map_conj_iff]
    have := (mem_normalizer_iff.1 (inv_mem hwaU.2) _).1 hvwU
    rw [inv_inv] at this
    exact (hUY.trans hYW) this
  have hwU : w ∈ d.U := G2Data.Q52.W_inf_map_wa_le_U d ⟨hw, hwW'⟩
  exact mul_mem (hD.U_le hwU) hu

theorem yamadaW₃_inf_yamadaC₁_le_W₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaW₃ d t ⊓ yamadaC₁ d t ≤ yamadaW₁ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, hYW, -, hWF, hFD, -, -, -, -⟩ := d.inclusions
  obtain ⟨hW₃V₃, -, -, hW₂W₃, htW₃, -, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, -, -, hV₃R₂, -, -, -, -, -⟩ := h.yamadaV₃_facts hW d hK hD
  intro x hx
  obtain ⟨hxW₃, hxC₁⟩ := Subgroup.mem_inf.1 hx
  have hxR₂ : x ∈ yamadaR₂ d t := h.yamadaC₁_le_yamadaR₂ d hK hxC₁
  have hxV₂ : x ∈ yamadaV₂ d t := by
    rw [← hV₃R₂]
    exact Subgroup.mem_inf.2 ⟨hW₃V₃ hxW₃, hxR₂⟩
  have h1 : x ∈ yamadaW₂ d t := by
    rcases (mem_sup_zpowers_iff_of h.t_mul_t (h.t_mem_normalizer_yamadaW₂ d hK hD).1).1 hxV₂ with
      h1 | ⟨a, ha, rfl⟩
    · exact h1
    · exfalso
      refine htW₃ ?_
      have := mul_mem (inv_mem (hW₂W₃ ha)) hxW₃
      rwa [inv_mul_cancel_left] at this
  obtain ⟨w, hw, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.yamadaY₂_le_normalizer_W d hK hD) _ h1
  have hwC₁ : w ∈ yamadaC₁ d t :=
    (le_sup_left.trans (h.tD_le_yamadaC₁ d hK)) ((hWF.trans hFD) hw)
  have hyC₁ : y ∈ yamadaC₁ d t := by
    have := mul_mem (inv_mem hwC₁) hxC₁
    rwa [inv_mul_cancel_left] at this
  have hyY₁ : y ∈ yamadaY₁ d t := by
    rw [← h.yamadaY₂_inf_yamadaR₁ d hK hD]
    exact ⟨hy, (le_sup_left : yamadaC₁ d t ≤ yamadaR₁ d t) hyC₁⟩
  have hY₁W₁ : yamadaY₁ d t ≤ yamadaW₁ d t := sup_le (hYW.trans le_sup_left) le_sup_right
  exact mul_mem (mem_sup_left hw) (hY₁W₁ hyY₁)

theorem yamadaW₃_inf_map_wa (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaW₃ d t ⊓ (yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom = yamadaU₁ d t := by
  have hD := hQ.doubling
  have hwa := d.wa_mem_inf_normalizer_U
  have hwaU₁ : d.wa ∈ normalizer (yamadaU₁ d t : Set G) :=
    hD.inf_normalizer_U_le_normalizer hK hwa
  have hwaC₁ : d.wa ∈ normalizer (yamadaC₁ d t : Set G) :=
    h.inf_normalizer_U_le_normalizer_yamadaC₁ d hwa
  have hwat : d.wa * t = t * d.wa := mem_centralizer_singleton_iff.1 (h.L_le_centralizer hwa.1)
  have hconjt' : d.wa⁻¹ * t * d.wa = t := by rw [mul_assoc, ← hwat, inv_mul_cancel_left]
  have hU₁W₃ := Q52.yamadaU₁_le_yamadaW₃ hW h d hK hD
  apply le_antisymm
  · intro x hx
    obtain ⟨hxW, hxW'⟩ := Subgroup.mem_inf.1 hx
    rw [mem_map_conj_iff] at hxW'
    have hκ1 := Q52.crossed_mem_yamadaW₁_of_mem_yamadaW₃ hW h d hK hD hxW
    have hκ2 := Q52.crossed_mem_yamadaW₁_of_mem_yamadaW₃ hW h d hK hD hxW'
    have hκU₁ : t * x * t * x⁻¹ ∈ yamadaU₁ d t := by
      refine Q52.mem_yamadaU₁_of_mem_yamadaW₁ h d hK hD hκ1 ?_
      have e : d.wa⁻¹ * (t * x * t * x⁻¹) * d.wa =
          t * (d.wa⁻¹ * x * d.wa) * t * (d.wa⁻¹ * x * d.wa)⁻¹ := by
        calc d.wa⁻¹ * (t * x * t * x⁻¹) * d.wa =
            (d.wa⁻¹ * t * d.wa) * (d.wa⁻¹ * x * d.wa) * (d.wa⁻¹ * t * d.wa) *
              (d.wa⁻¹ * x * d.wa)⁻¹ := by group
          _ = t * (d.wa⁻¹ * x * d.wa) * t * (d.wa⁻¹ * x * d.wa)⁻¹ := by rw [hconjt']
      rw [e]
      exact hκ2
    have hxC := (Q52.yamadaW₃_le hW h d hK hD).2.2.2 hxW
    have hxV : x ∈ h.yamadaV d hK hD := (h.yamadaCstar_eq d hK hD) ▸ hxC
    have hxC₁ : x ∈ yamadaC₁ d t := h.mem_yamadaC₁_of_crossed_mem d hK hD hxV hκU₁
    have hx1 := Q52.yamadaW₃_inf_yamadaC₁_le_W₁ hW h d hK hQ ⟨hxW, hxC₁⟩
    have hxC₁' : d.wa⁻¹ * x * d.wa ∈ yamadaC₁ d t := by
      have := (mem_normalizer_iff.1 (inv_mem hwaC₁) x).1 hxC₁
      rwa [inv_inv] at this
    have hx2 := Q52.yamadaW₃_inf_yamadaC₁_le_W₁ hW h d hK hQ ⟨hxW', hxC₁'⟩
    exact Q52.mem_yamadaU₁_of_mem_yamadaW₁ h d hK hD hx1 hx2
  · intro u hu
    refine Subgroup.mem_inf.2 ⟨hU₁W₃ hu, ?_⟩
    rw [mem_map_conj_iff]
    refine hU₁W₃ ?_
    have := (mem_normalizer_iff.1 (inv_mem hwaU₁) u).1 hu
    rwa [inv_inv] at this

theorem card_yamadaD₁ (h : Setup G L f t) (d : G2Data L K) (hD : h.DoublingFacts d) :
    Nat.card (yamadaD₁ d t) = Nat.card K ^ 6 := by
  have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaU₁ d t) (B := d.D)
    (fun x hx => Subgroup.centralizer_le_normalizer _ (hD.D_le_centralizer hx))
  rw [sup_comm, ← hD.D₁_eq, hD.inf_D, hD.card_eq, d.cards.1, d.cards.2.2.2.2.2.1] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [h1]
  ring

theorem card_yamadaCstar (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : Nat.card (yamadaCstar d t) = 2 * Nat.card K ^ 10 := by
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -, -, -, -⟩ := d.inclusions
  obtain ⟨⟨-, -, hC₁inf⟩, -⟩ := h.yamada_5_19 d hK hD
  have hC₁C : yamadaC₁ d t ≤ yamadaCstar d t := by
    rw [← hC₁inf]
    exact inf_le_left
  obtain ⟨_, _, φ, -, -⟩ := h.yamada_5_19_4 d hK hD
  have hUD : d.U ≤ d.D := hUY.trans (hYX.trans (hXF.trans hFD))
  have hq : 0 < Nat.card K := Nat.card_pos
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((yamadaC₁ d t).subgroupOf (yamadaCstar d t))
  rw [Nat.card_congr (subgroupOfEquivOfLe hC₁C).toEquiv, h.card_yamadaC₁ d hK,
    Q52.card_yamadaD₁ h d hD, Nat.card_congr φ.toEquiv] at e1
  have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (d.U.subgroupOf d.D)
  rw [Nat.card_congr (subgroupOfEquivOfLe hUD).toEquiv, d.cards.1, d.cards.2.2.2.2.2.1] at e2
  have e3 : Nat.card (d.D ⧸ d.U.subgroupOf d.D) = Nat.card K ^ 4 := by
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    rw [← e2]
    ring
  rw [e1, e3]
  ring

theorem card_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nat.card (yamadaD₇ d t) = Nat.card K ^ 10 := by
  have hD := hQ.doubling
  obtain ⟨-, -, hD₇C, htN, htD₇⟩ := h.yamada_5_51 hW d hK hQ
  have h1 := h.card_sup_zpowers htN htD₇
  rw [hD₇C] at h1
  have h2 := Q52.card_yamadaCstar h d hK hD
  have : yamadaC₇ d t = yamadaCstar d t := rfl
  rw [this, h2] at h1
  omega

theorem yamadaD₇_eq_yamadaW₃_sup_map (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaD₇ d t = yamadaW₃ d t ⊔ (yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom ∧
      (yamadaD₇ d t : Set G) = (yamadaW₃ d t : Set G) *
        ((yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom : Set G) ∧
      yamadaW₃ d t ⊓ (yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom = yamadaU₁ d t := by
  have hD := hQ.doubling
  have hWW := Q52.yamadaW₃_inf_map_wa hW h d hK hQ
  have hwaN := Q52.wa_mem_normalizer_yamadaD₇ hW h d hK hQ
  obtain ⟨-, -, -, hS₅S₆, hS₆P, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨hW₃L, -, -, hW₃C⟩ := Q52.yamadaW₃_le hW h d hK hD
  have hW₃S₅ : yamadaW₃ d t ≤ yamadaS₅ d t :=
    (le_sup_left : yamadaW₃ d t ≤ yamadaS₃ d t).trans le_sup_left
  have hW₃D₇ : yamadaW₃ d t ≤ yamadaD₇ d t := le_inf (hW₃S₅.trans (hS₅S₆.trans hS₆P)) hW₃C
  have hW₃aD₇ : (yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom ≤ yamadaD₇ d t := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 hwaN y).1 (hW₃D₇ hy)
  have hcard := Q52.card_coe_mul_mul_card_inf (yamadaW₃ d t)
    ((yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom)
  rw [hWW, hD.card_eq, card_map_conj, (h.yamadaW₃_facts hW d hK hD).2.2.2.2.2.2] at hcard
  have hDcard := Q52.card_yamadaD₇ hW h d hK hQ
  have hq : 0 < Nat.card K ^ 2 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have hX : Nat.card ((yamadaW₃ d t : Set G) *
      ((yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom : Set G)) = Nat.card K ^ 10 := by
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    rw [hcard]
    ring
  have hsub : (yamadaW₃ d t : Set G) *
      ((yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom : Set G) ⊆ (yamadaD₇ d t : Set G) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (hW₃D₇ ha) (hW₃aD₇ hb)
  have hprod : (yamadaW₃ d t : Set G) *
      ((yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom : Set G) = (yamadaD₇ d t : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hX]
    exact le_of_eq (by rw [← hDcard]; rfl)
  refine ⟨le_antisymm (fun x hx => ?_) (sup_le hW₃D₇ hW₃aD₇), hprod.symm, hWW⟩
  have hx' : x ∈ (yamadaD₇ d t : Set G) := hx
  rw [← hprod] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem crossed_mem_yamadaW₁_of_mem_yamadaC₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    {x : G} (hx : x ∈ yamadaC₃ d t) : t * x * t * x⁻¹ ∈ yamadaW₁ d t :=
  ((h.mem_yamadaR₃star_iff d hK hD).1 ((h.yamada_5_23_4 hW d hK hD) ▸ hx.1)).2

theorem yamadaD₁_le_yamadaD₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaD₁ d t ≤ yamadaD₃ d t := by
  have hD₁C₁ := h.yamadaD₁_le_yamadaC₁ d hK
  refine le_inf ((Q52.yamadaD₁_le_yamadaS₂ h d hD).trans le_sup_right) (le_inf ?_ ?_)
  · exact (hD₁C₁.trans (h.yamadaC₁_le_yamadaR₂ d hK)).trans (h.yamadaR₃_facts hW d hK hD).2.1
  · exact hD₁C₁.trans (Q52.yamadaC₁_le_yamadaCstar h d hK hD)

end Q52

theorem yamada_5_54_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaD₇ d t = yamadaD₃ d t ⊔ (yamadaD₃ d t).map (MulAut.conj d.wa).toMonoidHom ∧
      (yamadaD₇ d t : Set G) = (yamadaD₃ d t : Set G) *
        ((yamadaD₃ d t).map (MulAut.conj d.wa).toMonoidHom : Set G) ∧
      yamadaD₃ d t ⊓ (yamadaD₃ d t).map (MulAut.conj d.wa).toMonoidHom = yamadaD₁ d t := by
  have hD := hQ.doubling
  obtain ⟨h2a, h2b, -⟩ := Q52.yamadaD₇_eq_yamadaW₃_sup_map hW h d hK hQ
  have hwaN := Q52.wa_mem_normalizer_yamadaD₇ hW h d hK hQ
  obtain ⟨-, -, -, hS₅S₆, hS₆P, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨-, -, hW₃C₃, -⟩ := Q52.yamadaW₃_le hW h d hK hD
  have hD₃D₇ : yamadaD₃ d t ≤ yamadaD₇ d t :=
    le_inf (((inf_le_left : yamadaD₃ d t ≤ yamadaS₃ d t).trans
      (le_sup_left : yamadaS₃ d t ≤ yamadaS₅ d t)).trans (hS₅S₆.trans hS₆P))
      ((inf_le_right : yamadaD₃ d t ≤ yamadaC₃ d t).trans inf_le_right)
  have hW₃D₃ : yamadaW₃ d t ≤ yamadaD₃ d t := le_inf le_sup_left hW₃C₃
  have hD₃aD₇ : (yamadaD₃ d t).map (MulAut.conj d.wa).toMonoidHom ≤ yamadaD₇ d t := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 hwaN y).1 (hD₃D₇ hy)
  refine ⟨le_antisymm ?_ (sup_le hD₃D₇ hD₃aD₇), ?_, ?_⟩
  · rw [h2a]
    exact sup_le_sup hW₃D₃ (Subgroup.map_mono hW₃D₃)
  · refine Set.Subset.antisymm ?_ ?_
    · rw [h2b]
      exact Set.mul_subset_mul (SetLike.coe_subset_coe.2 hW₃D₃)
        (SetLike.coe_subset_coe.2 (Subgroup.map_mono hW₃D₃))
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact mul_mem (hD₃D₇ ha) (hD₃aD₇ hb)
  · have hwa := d.wa_mem_inf_normalizer_U
    have hwaD₁ : d.wa ∈ normalizer (yamadaD₁ d t : Set G) := (h.yamada_5_8_1 d hK).1 hwa
    have hwat : d.wa * t = t * d.wa := mem_centralizer_singleton_iff.1 (h.L_le_centralizer hwa.1)
    have hconjt' : d.wa⁻¹ * t * d.wa = t := by rw [mul_assoc, ← hwat, inv_mul_cancel_left]
    apply le_antisymm
    · intro x hx
      obtain ⟨hxD₃, hxD₃'⟩ := Subgroup.mem_inf.1 hx
      rw [mem_map_conj_iff] at hxD₃'
      have hxC₃ := (inf_le_right : yamadaD₃ d t ≤ yamadaC₃ d t) hxD₃
      have hyC₃ := (inf_le_right : yamadaD₃ d t ≤ yamadaC₃ d t) hxD₃'
      have hκ1 := Q52.crossed_mem_yamadaW₁_of_mem_yamadaC₃ hW h d hK hD hxC₃
      have hκ2 := Q52.crossed_mem_yamadaW₁_of_mem_yamadaC₃ hW h d hK hD hyC₃
      have hκU₁ : t * x * t * x⁻¹ ∈ yamadaU₁ d t := by
        refine Q52.mem_yamadaU₁_of_mem_yamadaW₁ h d hK hD hκ1 ?_
        have e : d.wa⁻¹ * (t * x * t * x⁻¹) * d.wa =
            t * (d.wa⁻¹ * x * d.wa) * t * (d.wa⁻¹ * x * d.wa)⁻¹ := by
          calc d.wa⁻¹ * (t * x * t * x⁻¹) * d.wa =
              (d.wa⁻¹ * t * d.wa) * (d.wa⁻¹ * x * d.wa) * (d.wa⁻¹ * t * d.wa) *
                (d.wa⁻¹ * x * d.wa)⁻¹ := by group
            _ = t * (d.wa⁻¹ * x * d.wa) * t * (d.wa⁻¹ * x * d.wa)⁻¹ := by rw [hconjt']
        rw [e]
        exact hκ2
      have hxC : x ∈ yamadaCstar d t := (inf_le_right : yamadaC₃ d t ≤ yamadaCstar d t) hxC₃
      have hxV : x ∈ h.yamadaV d hK hD := (h.yamadaCstar_eq d hK hD) ▸ hxC
      have hxC₁ : x ∈ yamadaC₁ d t := h.mem_yamadaC₁_of_crossed_mem d hK hD hxV hκU₁
      exact Q52.yamadaC₁_inf_yamadaD₇_le hW h d hK hQ ⟨hxC₁, hD₃D₇ hxD₃⟩
    · intro x hx
      refine Subgroup.mem_inf.2 ⟨Q52.yamadaD₁_le_yamadaD₃ hW h d hK hD hx, ?_⟩
      rw [mem_map_conj_iff]
      refine Q52.yamadaD₁_le_yamadaD₃ hW h d hK hD ?_
      have := (mem_normalizer_iff.1 (inv_mem hwaD₁) x).1 hx
      rwa [inv_inv] at this

theorem yamada_5_54_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaD₇ d t = yamadaW₃ d t ⊔ (yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom ∧
      (yamadaD₇ d t : Set G) = (yamadaW₃ d t : Set G) *
        ((yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom : Set G) ∧
      yamadaW₃ d t ⊓ (yamadaW₃ d t).map (MulAut.conj d.wa).toMonoidHom = yamadaU₁ d t :=
  Q52.yamadaD₇_eq_yamadaW₃_sup_map hW h d hK hQ

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
