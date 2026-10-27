module

public import CFSG.ClassicalInvolution.Q3.TL4D1Fin
public import CFSG.ClassicalInvolution.Q3.TL4D1Out
public import CFSG.ClassicalInvolution.Q3.TL3T14
public import CFSG.ClassicalInvolution.Q3.TL4D1Lift
public import CFSG.ClassicalInvolution.Q3.TL4D1Sub

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

omit [Finite G] in
theorem false_of_e8_top {E : Subgroup G} (hE : E8Struct ⊤ E) {u v : G} (hu : TightInO2 u)
    (hv : TightInO2 v) (huv : u * v ≠ v * u) : False := by
  have hQE : pCore 2 G ≤ E := hE.core _ le_top (fun x _ q hq => pCore_normal.conj_mem q hq x)
    pCore_isPGroup
  exact huv (comm_of_sq hE.sq (hQE (mem_pCore_of_tightInO2 hu)) (hQE (mem_pCore_of_tightInO2 hv)))

theorem false_of_ident_top (h : T4Hyp 3 G Δ)
    (hall : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → TightInO2 z) {P : Set (Subgroup G)}
    (hPΔ : P ⊆ Δ) (htop : pSpan P = ⊤) {n : ℕ} (hn : 5 ≤ n) {𝒜 : Set (Finset (Fin n))}
    {M : Subgroup (AE.AEQ n)} (hMem : ModelMembers 𝒜 M) (I : AEIdentOn P n 𝒜 M)
    {L : Subgroup G} (hL : L ∈ Δ) (hLP : L ∉ P) {v : G} (hv : IsUniqueInvolution L v)
    (hvZ : ∃ g : G, g * v ≠ v * g)
    (hthin : ∀ T : Subgroup G, T.Normal → IsPGroup 2 T → ∀ x ∈ L, x ∈ T → x = 1 ∨ x = v) :
    False := by
  set X := pSpan P with hXdef
  have hX : ∀ g : G, g ∈ X := fun g => htop ▸ Subgroup.mem_top g
  have h2 : ∀ K ∈ Δ, IsPGroup 2 K := fun K hK => h.isPGroup_of_all hall hK
  have h8 : ∀ K ∈ Δ, Nat.card K = 8 := fun K hK => h.card_eq_eight hK (h2 K hK)
  have hodd : classicalInvolutionOddCore ↥X = ⊥ :=
    oddCore_eq_bot_of_isSubnormal h.odd (htop ▸ Subgroup.IsSubnormal.top)
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hodd
  have hLX : L ≤ X := fun x _ => hX x
  have hcen : ∀ {c : ↥X}, c ∈ I.φ.ker → ∀ g : G, g * c = c * g :=
    fun hc g => comm_of_mem_center (I.ker_le hc) (hX g)
  have hvZ' : (⟨v, hLX hv.mem⟩ : ↥X) ∉ Subgroup.center ↥X := by
    intro hc
    obtain ⟨g, hg⟩ := hvZ
    exact hg (comm_of_mem_center hc (hX g))
  have hinj : ∀ {l₁ l₂ : G}, l₁ ∈ L → l₂ ∈ L → I.φ ⟨l₁, hX l₁⟩ = I.φ ⟨l₂, hX l₂⟩ → l₁ = l₂ :=
    fun h₁ h₂ he => injOn_of_not_mem_center I.φ I.ker_le hLX (h2 L hL) hv hvZ' h₁ h₂ he
  have hrange : M ≤ I.φ.range := I.range_eq.ge
  have hrangeM : I.φ.range ≤ M := I.range_eq.le
  set B := (L.subgroupOf X).map I.φ with hB
  set w := I.φ ⟨v, hX v⟩ with hw
  have hmemB : ∀ {l : G} (hl : l ∈ L), I.φ ⟨l, hX l⟩ ∈ B :=
    fun hl => ⟨_, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hofB : ∀ {x}, x ∈ B → ∃ l ∈ L, I.φ ⟨l, hX l⟩ = x := by
    rintro _ ⟨⟨l, hlX⟩, hl, rfl⟩
    exact ⟨l, Subgroup.mem_subgroupOf.mp hl, rfl⟩
  have hBM : B ≤ M := (Subgroup.map_le_range _ _).trans I.range_eq.le
  have hBu : IsUniqueInvolution B w := by
    refine ⟨hmemB hv.mem, fun h1 => hv.ne_one ?_, ?_, fun y hy hy2 => ?_⟩
    · exact hinj hv.mem L.one_mem (by rw [← hw, h1, ← map_one I.φ]; rfl)
    · rw [hw, ← map_mul, ← map_one I.φ]
      exact congrArg I.φ (Subtype.ext hv.sq)
    · obtain ⟨l, hl, rfl⟩ := hofB hy
      have hl2 : l * l = 1 := hinj (L.mul_mem hl hl) L.one_mem (by
        rw [show (⟨l * l, hX _⟩ : ↥X) = ⟨l, hX l⟩ * ⟨l, hX l⟩ from rfl, map_mul, hy2,
          show (⟨1, hX 1⟩ : ↥X) = 1 from rfl, map_one])
      rcases hv.unique l hl hl2 with rfl | rfl
      · left
        exact (map_one I.φ ▸ rfl)
      · right
        rfl
  have hcard : Nat.card ↥B = 8 := by
    let f : ↥(L.subgroupOf X) → ↥B := fun x => ⟨I.φ x, ⟨x, x.2, rfl⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨fun a b hab => ?_, fun ⟨y, hy⟩ => ?_⟩
      · have := hinj (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)
          (congrArg Subtype.val hab)
        exact Subtype.ext (Subtype.ext this)
      · obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv, h8 L hL]
  have hnab : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x := by
    obtain ⟨-, S, hS, hSnc⟩ := h.hyp.omega1 L hL
    by_contra hc
    push Not at hc
    refine hSnc ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have ha := hS.1 a.2
    have hb := hS.1 b.2
    refine hinj (L.mul_mem ha hb) (L.mul_mem hb ha) ?_
    show I.φ ⟨(a : G) * b, hX _⟩ = I.φ ⟨(b : G) * a, hX _⟩
    rw [show (⟨a * b, hX _⟩ : ↥X) = ⟨a, hX a⟩ * ⟨b, hX b⟩ from rfl,
      show (⟨b * a, hX _⟩ : ↥X) = ⟨b, hX b⟩ * ⟨a, hX a⟩ from rfl, map_mul, map_mul]
    exact hc _ (hmemB ha) _ (hmemB hb)
  have hTex : ∃ T : Subgroup (AE.AEQ n), T ≤ M ∧ (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) ∧
      IsPGroup 2 ↥T ∧ w ∈ T := by
    refine ⟨((pCore 2 G).subgroupOf X).map I.φ,
      (Subgroup.map_le_range _ _).trans I.range_eq.le, ?_,
      (pCore_isPGroup.comap_subtype).map _, ⟨_, ?_, rfl⟩⟩
    · rintro x hx _ ⟨t, ht, rfl⟩
      obtain ⟨g, rfl⟩ := hrange hx
      refine ⟨g * t * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp only [map_mul, map_inv]⟩
      simpa using pCore_normal.conj_mem _ (Subgroup.mem_subgroupOf.mp ht) g
    · exact Subgroup.mem_subgroupOf.mpr (mem_pCore_of_tightInO2 (hall L hL v hv))
  have hTthin : ∀ T : Subgroup (AE.AEQ n), T ≤ M → (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) →
      IsPGroup 2 ↥T → ∀ x ∈ B, x ∈ T → x = 1 ∨ x = w := by
    intro T _ hTn hT2 x hx hxT
    obtain ⟨l, hl, rfl⟩ := hofB hx
    set T' : Subgroup G := (T.comap I.φ).map X.subtype with hT'
    have hT'n : T'.Normal := ⟨by
      rintro _ ⟨t, ht, rfl⟩ g
      refine ⟨⟨g, hX g⟩ * t * ⟨g, hX g⟩⁻¹, ?_, rfl⟩
      show I.φ (⟨g, hX g⟩ * t * ⟨g, hX g⟩⁻¹) ∈ T
      rw [map_mul, map_mul, map_inv]
      exact hTn _ (hrangeM ⟨_, rfl⟩) _ ht⟩
    have hT'2 : IsPGroup 2 ↥T' := (hT2.comap_of_ker_isPGroup I.φ hk).map _
    rcases hthin T' hT'n hT'2 l hl ⟨⟨l, hX l⟩, hxT, rfl⟩ with rfl | rfl
    · exact Or.inl (map_one I.φ ▸ rfl)
    · exact Or.inr rfl
  have hodd3 : ∀ y ∈ M, Odd (orderOf y) → y * w = w * y → ∀ x ∈ B, y * x * y⁻¹ ∈ B := by
    intro y hy hyo hyw x hx
    obtain ⟨y', rfl, hy'o⟩ := exists_lift_odd I.φ (hrange hy) hyo
    have hc := comm_of_odd_of_map_comm I.φ I.ker_le hk hy'o hyw
    have hyC : (y' : G) ∈ Subgroup.centralizer ({v} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc)
    have hyN := h.tight L hL v hv hyC
    obtain ⟨l, hl, rfl⟩ := hofB hx
    have hl' : (y' : G) * l * (y' : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN l).mp hl
    have := hmemB hl'
    rwa [show (⟨(y' : G) * l * (y' : G)⁻¹, hX _⟩ : ↥X) = y' * ⟨l, hX l⟩ * y'⁻¹ from rfl,
      map_mul, map_mul, map_inv] at this
  have hmem' : ∀ α ∈ 𝒜, ∀ (h' : α.card = 4) (b : Bool), AE.zBar α h' = w →
      AE.memBar α h' b = B ∨ Commutes (AE.memBar α h' b) B := by
    intro α hα h' b hzw
    obtain ⟨K, hKP, hKlab⟩ := I.label_surj α hα h' b
    obtain ⟨⟨u', hu'⟩, -⟩ := h.hyp.omega1 K (hPΔ hKP)
    have hφu' := phi_map_eq_zBar I.φ hn hKP (h8 K (hPΔ hKP)) hKlab hu'
    set c : ↥X := (⟨u', le_pSpan hKP hu'.mem⟩ : ↥X)⁻¹ * ⟨v, hX v⟩ with hc
    have hcker : c ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, hc, map_mul, map_inv, hφu', hzw, inv_mul_cancel]
    have hvc : v = u' * c := by simp [hc]
    rcases h.eq_or_commutes_of_mul_center h2 (hPΔ hKP) hL hu' hv (hcen hcker) hvc with
      heq | hcomm
    · left
      rw [← hKlab, heq]
    · right
      intro x hx y hy
      rw [← hKlab] at hx
      obtain ⟨⟨a, haX⟩, ha, rfl⟩ := hx
      obtain ⟨l, hl, rfl⟩ := hofB hy
      rw [← map_mul, ← map_mul]
      exact congrArg I.φ (Subtype.ext (hcomm a (Subgroup.mem_subgroupOf.mp ha) l hl))
  have hconj : ∀ g ∈ M, g * w = w * g → conjSub g B = B ∨ Commutes B (conjSub g B) := by
    intro g hg hgw
    obtain ⟨g', rfl⟩ := hrange hg
    obtain ⟨c, hcker, hce⟩ := conj_eq_mul_of_map_comm I.φ hgw
    have hL' : conjSub (g' : G) L ∈ Δ := h.hyp.conjInvariant g' L hL
    have hab : (g' : G) * v * (g' : G)⁻¹ = v * c := congrArg Subtype.val hce
    have hmap : ((conjSub (g' : G) L).subgroupOf X).map I.φ = conjSub (I.φ g') B :=
      map_conjSub_subgroupOf I.φ L (hX g')
    rcases h.eq_or_commutes_of_mul_center h2 hL hL' hv (hv.conj g') (hcen hcker) hab with
      heq | hcomm
    · left
      rw [← hmap, ← heq]
    · right
      rw [← hmap]
      intro x hx y hy
      obtain ⟨l, hl, rfl⟩ := hofB hx
      obtain ⟨⟨l', hl'X⟩, hl', rfl⟩ := hy
      rw [← map_mul, ← map_mul]
      exact congrArg I.φ (Subtype.ext (hcomm l hl l' (Subgroup.mem_subgroupOf.mp hl')))
  obtain ⟨α, hα, h', b, hBeq⟩ := hMem B w hBM hBu hcard hnab hTex hTthin hodd3 hmem' hconj
  obtain ⟨K, hKP, hKlab⟩ := I.label_surj α hα h' b
  have hKL : K = L := eq_of_map_le_memBar h.hyp h2 hn I.φ hk (hPΔ hKP) hL (le_pSpan hKP) hLX
    hKlab (by rw [hKlab, ← hBeq])
  exact hLP (hKL ▸ hKP)

end CFSG.ClassicalInvolution.Q3.TL4
