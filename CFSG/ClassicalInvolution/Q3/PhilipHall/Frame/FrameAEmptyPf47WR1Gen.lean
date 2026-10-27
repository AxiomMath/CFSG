module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WR1Conj
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WR1Ind
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf16Thm3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecQuot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3D8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3D8A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3Datum
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf4X
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf5Alpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf6C205
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf6Orb
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf8Alpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf9C178
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf9C206
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Wire
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSecNoExit
public import CFSG.ClassicalInvolution.Q3.Q3T6D8
public import CFSG.ClassicalInvolution.Q3.Q3T6D8A
public import CFSG.ClassicalInvolution.Q3.Q3T6DC3
public import CFSG.ClassicalInvolution.Q3.Q3T6DC7
public import CFSG.ClassicalInvolution.Q3.Q3T6DCaseIC
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Twin
public import CFSG.ClassicalInvolution.Q3.Q3T6DSOrb
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22H51uC
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Rank

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.WR1

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

set_option hygiene false in
local notation "𝕌𝕍" => (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G)
set_option hygiene false in
local notation "𝕏𝕏" =>
  ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) : Subgroup G)
set_option hygiene false in
local notation "𝕐𝕐" => (pairNormalizers K J z j)
set_option hygiene false in
local notation "πN" => (QuotientGroup.mk' (classicalInvolutionOddCore G))
set_option hygiene false in
local notation "𝕄" => ((W.map (QuotientGroup.mk' (classicalInvolutionOddCore G))).comap
  (QuotientGroup.mk' (classicalInvolutionOddCore G)))

variable {Ω : Set (Subgroup G)}

theorem card_le_four_of_abelian (hΩ : TypeRHyp Ω) {L : Subgroup G} (hL : L ∈ Ω) {A : Subgroup G}
    (hAL : A ≤ L) (hA : IsPGroup 2 A) (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ≤ 4 := by
  obtain ⟨P, hP, hAP⟩ := IsSylow2In.exists_ge hA hAL
  obtain ⟨e⟩ := hΩ.sylow L hL P hP
  have hP8 : Nat.card P = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hdvd : Nat.card A ∣ 8 := hP8 ▸ Subgroup.card_dvd_of_le hAP
  have hne : Nat.card A ≠ 8 := by
    intro h8
    have hPA : P ≤ A := (Subgroup.eq_of_le_of_card_ge hAP (by rw [hP8, h8])).ge
    have h1 := hab _ (hPA (e.symm (QuaternionGroup.a 1)).2) _ (hPA (e.symm (QuaternionGroup.xa 0)).2)
    have h2 : e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) =
        e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) := Subtype.ext h1
    rw [← map_mul, ← map_mul] at h2
    exact absurd (e.symm.injective h2) (by decide)
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hle : Nat.card A ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card A <;> omega

namespace Data

variable {K J K' W : Subgroup G} {z j u v : G} {R R' T : Subgroup G}
  (d : Data Ω K J K' W z j u v R R' T)
include d

theorem eq_of_mem_UV_of_sq {x : G} (hx : x ∈ 𝕌𝕍) (hx2 : x * x = 1) :
    x = 1 ∨ x = z ∨ x = j ∨ x = z * j := by
  obtain ⟨a, ha, b, hb, rfl⟩ := d.tor.exists_mul_of_mem_UV hx
  have hab : a * b = b * a := d.tor.hcomm a ha b hb
  have h1 : a * a = (b * b)⁻¹ := by
    have : a * a * (b * b) = 1 := by
      calc a * a * (b * b) = a * b * (a * b) := by
            rw [show a * b * (a * b) = a * (b * a) * b by group, ← hab]; group
        _ = 1 := hx2
    exact eq_inv_of_mul_eq_one_left this
  have h2 : a * a ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v :=
    ⟨Subgroup.mul_mem _ ha ha, h1 ▸ Subgroup.inv_mem _ (Subgroup.mul_mem _ hb hb)⟩
  rw [d.tor.U_inf_V, Subgroup.mem_bot] at h2
  have h3 : b * b = 1 := by
    rw [h2] at h1
    exact inv_eq_one.mp h1.symm
  rcases d.tor.hz.unique a (d.tor.hUK ha) h2 with rfl | rfl <;>
    rcases d.tor.hj.unique b (d.tor.hVJ hb) h3 with rfl | rfl
  · left
    group
  · right; right; left
    group
  · right; left
    group
  · right; right; right
    rfl

theorem inv_eq (hΩ : TypeRHyp Ω) (hall : aStar Ω K = Ω)
    (hsurj : ∀ g : G, ∃ y ∈ 𝕐𝕐, ∃ w ∈ W, πN g = πN (y * w)) {L : Subgroup G} (hL : L ∈ Ω)
    {l : G} (hl : IsUniqueInvolution L l) (hlW : l ∈ W) : l = z ∨ l = j ∨ l = z * j := by
  have hLa : L ∈ aStar Ω K := by
    rw [hall]
    exact hL
  obtain ⟨-, hconj⟩ := exists_conj_of_mem_aStar hΩ.hyp d.tor.hK d.tor.hz hLa
  obtain ⟨g, hg⟩ := hconj l hl
  obtain ⟨y, hy, w, hw, hgyw⟩ := hsurj g
  have hyz : y * z * y⁻¹ ∈ 𝕌𝕍 := by
    have h1 : y * z * y⁻¹ ∈ (Subgroup.closure ({z, j} : Set G) : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp (d.tor.hYZ hy) z).mp (Subgroup.subset_closure (by simp))
    exact d.tor.Z_le_UV h1
  have hwz : w * z = z * w := d.hWab w hw z d.z_mem_W
  have hconj' : (y * w) * z * (y * w)⁻¹ = y * z * y⁻¹ := by
    calc (y * w) * z * (y * w)⁻¹ = y * (w * z) * w⁻¹ * y⁻¹ := by group
      _ = y * (z * w) * w⁻¹ * y⁻¹ := by rw [hwz]
      _ = y * z * y⁻¹ := by group
  have hπ : πN l = πN (y * z * y⁻¹) := by
    calc πN l = πN (g * z * g⁻¹) := by rw [hg]
      _ = πN g * πN z * (πN g)⁻¹ := by simp only [map_mul, map_inv]
      _ = πN (y * w) * πN z * (πN (y * w))⁻¹ := by rw [hgyw]
      _ = πN ((y * w) * z * (y * w)⁻¹) := by simp only [map_mul, map_inv]
      _ = πN (y * z * y⁻¹) := by rw [hconj']
  have hl' : l = y * z * y⁻¹ := eq_of_mk_eq d.hW2 hlW (d.UV_le_W hyz) hπ
  have hsq : (y * z * y⁻¹) * (y * z * y⁻¹) = 1 := by
    rw [show (y * z * y⁻¹) * (y * z * y⁻¹) = y * (z * z) * y⁻¹ by group, d.tor.hz.sq]
    group
  rcases d.eq_of_mem_UV_of_sq hyz hsq with h | h | h | h
  · exact absurd (hl'.trans h) hl.ne_one
  · exact Or.inl (hl'.trans h)
  · exact Or.inr (Or.inl (hl'.trans h))
  · exact Or.inr (Or.inr (hl'.trans h))

theorem exists_conj_z {l : G} (hl : l = z ∨ l = j ∨ l = z * j) :
    ∃ y ∈ Subgroup.normalizer (𝕌𝕍 : Set G), y * l * y⁻¹ = z := by
  obtain ⟨r, hr, hru⟩ := d.tor.exists_r
  obtain ⟨t, ht, htv⟩ : ∃ t ∈ T, t ∉ Subgroup.zpowers v := by
    by_contra h
    push Not at h
    have h1 := d.tor.card_sylow_eq d.tor.hJ d.tor.hV d.tor.hVJ d.tor.hT
    have h2 : Nat.card T ≤ Nat.card (Subgroup.zpowers v) := Subgroup.card_le_of_le h
    have h3 := d.tor.V_data.2
    omega
  have hrj := d.tor.he1 r hr hru
  have htz := d.tor.he2 t ht htv
  have hrN := d.tor.hRN hr
  have htN := d.tor.hTN ht
  rcases hl with h | h | h
  · exact ⟨1, Subgroup.one_mem _, by rw [h]; group⟩
  · refine ⟨t⁻¹ * r, Subgroup.mul_mem _ (Subgroup.inv_mem _ htN) hrN, ?_⟩
    rw [h]
    calc t⁻¹ * r * j * (t⁻¹ * r)⁻¹ = t⁻¹ * (r * j * r⁻¹) * t := by group
      _ = t⁻¹ * (t * z * t⁻¹) * t := by rw [hrj, htz]
      _ = z := by group
  · refine ⟨t⁻¹, Subgroup.inv_mem _ htN, ?_⟩
    rw [h]
    calc t⁻¹ * (z * j) * t⁻¹⁻¹ = t⁻¹ * (t * z * t⁻¹) * t := by rw [htz, inv_inv]
      _ = z := by group

theorem inf_W_le (hΩ : TypeRHyp Ω) (hall : aStar Ω K = Ω)
    (hsurj : ∀ g : G, ∃ y ∈ 𝕐𝕐, ∃ w ∈ W, πN g = πN (y * w)) {L : Subgroup G} (hL : L ∈ Ω)
    {U₀ : Subgroup G} (hU₀ : U₀ ∈ USet Ω) (hU₀L : U₀ ≤ L) (hU₀W : U₀ ≤ W) : L ⊓ W ≤ 𝕌𝕍 := by
  obtain ⟨l, hl⟩ := Sec6Gen.exists_uniqueInvolution hΩ.hyp hL
  obtain ⟨-, -, -, -, -, -, -, -, hU₀4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ.hyp hU₀
  have hlU₀ : l ∈ U₀ :=
    hl.mem_of_le hU₀L (Sec6Gen.isPGroup_of_mem_USet hΩ.hyp hU₀) (by omega)
  obtain ⟨y, hyN, hyl⟩ := d.exists_conj_z (d.inv_eq hΩ hall hsurj hL hl (hU₀W hlU₀))
  have hyE : conjSub y 𝕌𝕍 = 𝕌𝕍 := mem_normalizer_iff_conjSub_eq.mp hyN
  have hLy : conjSub y L ∈ twinSet Ω K := by
    refine ⟨hΩ.hyp.conjInvariant y L hL, z, d.tor.hz, ?_⟩
    rw [← hyl]
    exact hl.conj y
  rw [d.tor.htw] at hLy
  have hWy2 : IsPGroup 2 (conjSub y W) := isPGroup_conjSub y d.hW2
  have hWyab : ∀ a ∈ conjSub y W, ∀ b ∈ conjSub y W, a * b = b * a := by
    intro a ha b hb
    rw [mem_conjSub_iff] at ha hb
    have h := d.hWab _ ha _ hb
    calc a * b = y * ((y⁻¹ * a * y) * (y⁻¹ * b * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * b * y) * (y⁻¹ * a * y)) * y⁻¹ := by rw [h]
      _ = b * a := by group
  have hEWy : 𝕌𝕍 ≤ conjSub y W := by
    have h := conjSub_mono (n := y) d.UV_le_W
    rwa [hyE] at h
  have key : ∀ M ∈ Ω, ∀ U₁ ∈ USet Ω, U₁ ≤ M → U₁ ≤ 𝕌𝕍 → M ⊓ conjSub y W ≤ 𝕌𝕍 := by
    intro M hM U₁ hU₁ hU₁M hU₁E
    obtain ⟨-, -, -, -, -, -, -, -, hU₁4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ.hyp hU₁
    have hle : U₁ ≤ M ⊓ conjSub y W := le_inf hU₁M (hU₁E.trans hEWy)
    have h4 := card_le_four_of_abelian hΩ hM inf_le_left (hWy2.to_le inf_le_right)
      (fun a ha b hb => hWyab a ha.2 b hb.2)
    have heq : U₁ = M ⊓ conjSub y W := Subgroup.eq_of_le_of_card_ge hle (by omega)
    rw [← heq]
    exact hU₁E
  have hLW : conjSub y (L ⊓ W) ≤ 𝕌𝕍 := by
    rw [conjSub_inf]
    rcases hLy with h | h
    · rw [h]
      exact key K d.tor.hK _ d.tor.hU d.tor.hUK le_sup_left
    · rw [h]
      obtain ⟨u', hu', hu'U, hEu'⟩ := d.tor.hU'
      have hu'K : Subgroup.zpowers u' ≤ K' := by
        rw [hu']
        exact inf_le_left.trans d.tor.hR'.1
      have hu'E : Subgroup.zpowers u' ≤ 𝕌𝕍 := by
        rw [hEu']
        exact le_sup_left
      exact key K' d.tor.hK' _ hu'U hu'K hu'E
  have h := conjSub_mono (n := y⁻¹) hLW
  rwa [conjSub_inv_conjSub,
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer _).inv_mem hyN)] at h

theorem W_eq (hΩ : TypeRHyp Ω) (hall : aStar Ω K = Ω)
    (hsurj : ∀ g : G, ∃ y ∈ 𝕐𝕐, ∃ w ∈ W, πN g = πN (y * w)) : W = 𝕌𝕍 := by
  refine le_antisymm ?_ d.UV_le_W
  obtain ⟨η, ⟨S', hη', -⟩, hWη⟩ := d.hW
  have hle : ∀ U₀ ∈ η, U₀ ≤ W := fun U₀ hU₀ => by
    rw [hWη]
    exact le_iSup₂ (f := fun V (_ : V ∈ η) => V) U₀ hU₀
  have hWη' : W ≤ ⨆ U ∈ η, U := hWη.le
  refine hWη'.trans (iSup₂_le fun U₀ hU₀ => ?_)
  have hU₀U : U₀ ∈ USet Ω := (hη'.1 hU₀).1
  obtain ⟨L, hL, hU₀L⟩ := Sec6Gen.exists_member_of_mem_USet hΩ.hyp hU₀U
  exact (le_inf hU₀L (hle U₀ hU₀)).trans (d.inf_W_le hΩ hall hsurj hL hU₀U hU₀L (hle U₀ hU₀))

theorem nonempty_equiv_UV (hΩ : TypeRHyp Ω) :
    Nonempty (↥𝕌𝕍 ≃* Multiplicative (ZMod 4 × ZMod 4)) := by
  have hUab : ∀ a ∈ Subgroup.zpowers u, ∀ b ∈ Subgroup.zpowers u, a * b = b * a :=
    fun a ha b hb => d.tor.UV_comm a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_left hb)
  have hVab : ∀ a ∈ Subgroup.zpowers v, ∀ b ∈ Subgroup.zpowers v, a * b = b * a :=
    fun a ha b hb => d.tor.UV_comm a (Subgroup.mem_sup_right ha) b (Subgroup.mem_sup_right hb)
  have hu4 : orderOf u = 4 := by
    have h1 := d.tor.U_data.2
    have h2 := card_le_four_of_abelian hΩ d.tor.hK d.tor.hUK d.tor.U_data.1 hUab
    rw [← Nat.card_zpowers]
    omega
  have hv4 : orderOf v = 4 := by
    have h1 := d.tor.V_data.2
    have h2 := card_le_four_of_abelian hΩ d.tor.hJ d.tor.hVJ d.tor.V_data.1 hVab
    rw [← Nat.card_zpowers]
    omega
  have hc : Commute u v := d.tor.hcomm u (Subgroup.mem_zpowers u) v (Subgroup.mem_zpowers v)
  have hpow : ∀ (g : G) (n : ℕ), orderOf g = 4 → g ^ (n % 4) = g ^ n := fun g n hg => by
    rw [← hg]
    exact pow_mod_orderOf g n
  let f : Multiplicative (ZMod 4 × ZMod 4) →* G :=
    MonoidHom.mk' (fun p => u ^ (Multiplicative.toAdd p).1.val * v ^ (Multiplicative.toAdd p).2.val)
      (by
        intro p q
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
        rw [hpow u _ hu4, hpow v _ hv4, pow_add, pow_add]
        have h1 : v ^ (Multiplicative.toAdd p).2.val * u ^ (Multiplicative.toAdd q).1.val =
            u ^ (Multiplicative.toAdd q).1.val * v ^ (Multiplicative.toAdd p).2.val :=
          (hc.symm.pow_pow _ _).eq
        calc u ^ (Multiplicative.toAdd p).1.val * u ^ (Multiplicative.toAdd q).1.val *
              (v ^ (Multiplicative.toAdd p).2.val * v ^ (Multiplicative.toAdd q).2.val)
            = u ^ (Multiplicative.toAdd p).1.val * (u ^ (Multiplicative.toAdd q).1.val *
              v ^ (Multiplicative.toAdd p).2.val) * v ^ (Multiplicative.toAdd q).2.val := by group
          _ = u ^ (Multiplicative.toAdd p).1.val * (v ^ (Multiplicative.toAdd p).2.val *
              u ^ (Multiplicative.toAdd q).1.val) * v ^ (Multiplicative.toAdd q).2.val := by
            rw [h1]
          _ = _ := by group)
  have hfE : ∀ p, f p ∈ 𝕌𝕍 := fun p =>
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _))
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers v) _))
  let f' : Multiplicative (ZMod 4 × ZMod 4) →* ↥𝕌𝕍 := f.codRestrict _ hfE
  have hval : ∀ {g : G} {a : ZMod 4}, orderOf g = 4 → g ^ a.val = 1 → a = 0 := by
    intro g a hg h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hg] at h1
    have h2 := ZMod.val_lt a
    have h3 : a.val = 0 := by omega
    exact (ZMod.val_eq_zero a).mp h3
  have hinj : Function.Injective f' := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hp' : u ^ (Multiplicative.toAdd p).1.val * v ^ (Multiplicative.toAdd p).2.val = 1 :=
      congrArg Subtype.val hp
    have h1 : u ^ (Multiplicative.toAdd p).1.val ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v := by
      refine ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hp']
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers v) _)
    rw [d.tor.U_inf_V, Subgroup.mem_bot] at h1
    have h2 : v ^ (Multiplicative.toAdd p).2.val = 1 := by
      rw [h1, one_mul] at hp'
      exact hp'
    have ha := hval hu4 h1
    have hb := hval hv4 h2
    have h0 : Multiplicative.toAdd p = 0 := Prod.ext ha hb
    exact h0
  have hcard : Nat.card ↥𝕌𝕍 = 16 := by
    have h := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer
      (AscL62.le_normalizer_of_commutes d.tor.hcomm)
    rw [d.tor.U_inf_V, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hu4,
      hv4] at h
    exact h
  have hbij : Function.Bijective f' := hinj.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_eq_fintype_card]
    rfl)
  exact ⟨(MulEquiv.ofBijective f' hbij).symm⟩

theorem centralizer_eq (hXM : 𝕏𝕏 ≤ 𝕄)
    (hsurj : ∀ g : G, ∃ y ∈ 𝕐𝕐, ∃ w ∈ W, πN g = πN (y * w)) (hWE : W = 𝕌𝕍) :
    Subgroup.centralizer ((W.map πN : Subgroup (G ⧸ classicalInvolutionOddCore G)) :
      Set (G ⧸ classicalInvolutionOddCore G)) = W.map πN := by
  have hEX := d.isSylow2In_UV d.tor.UV_le_X d.tor.hXY hXM
  apply le_antisymm
  · intro gb hgb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore G) gb
    obtain ⟨y, hy, w, hw, hgyw⟩ := hsurj g
    have hyc : ∀ e ∈ 𝕌𝕍, πN y * πN e = πN e * πN y := by
      intro e he
      have heW : πN e ∈ W.map πN := Subgroup.mem_map_of_mem _ (d.UV_le_W he)
      have h1 : Commute (πN g) (πN e) := (Subgroup.mem_centralizer_iff.mp hgb (πN e) heW).symm
      have h2 : Commute (πN w) (πN e) := d.mk_comm (d.W_le_M hw) (d.W_le_M (d.UV_le_W he))
      have h3 : πN y = πN g * (πN w)⁻¹ := by
        rw [hgyw, map_mul]
        group
      rw [h3]
      exact (h1.mul_left h2.inv_left).eq
    have hyX : y ∈ 𝕏𝕏 := d.mem_X_of_conj hEX le_rfl hXM hy
      (mem_normalizer_iff_conjSub_eq.mp (d.tor.hYX hy)) hyc
    rw [hgyw, map_mul]
    exact Subgroup.mul_mem _ (hXM hyX) (Subgroup.mem_map_of_mem _ hw)
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    exact d.mk_comm (d.W_le_M hb') (d.W_le_M ha')

end Data

theorem w_struct_gen (hΩ : TypeRHyp Ω) {K : Subgroup G} (hK : K ∈ Ω) (hA : ¬ AEmpty Ω K)
    (hall : aStar Ω K = Ω) {W : Subgroup (G ⧸ classicalInvolutionOddCore G)} [W.Normal]
    (hW : WSet (oddQuotientFamily Ω) = {W})
    (hD : Nonempty (((G ⧸ classicalInvolutionOddCore G) ⧸ W) ≃* DihedralGroup 6)) :
    Nonempty (↥W ≃* Multiplicative (ZMod 4 × ZMod 4)) ∧
      Subgroup.centralizer (W : Set (G ⧸ classicalInvolutionOddCore G)) = W := by
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hA
  obtain ⟨K', W₀, u, v, R, R', T, d⟩ :=
    exists_data hΩ.hyp hK hv.mem (inA_of_aViol hv) hv.hzK hv.hzJ
  have hN : Odd (Nat.card (classicalInvolutionOddCore G)) :=
    CFSG.ComponentClassification.OddCore.odd_card G
  have hmap : W₀.map πN ∈ WSet (oddQuotientFamily Ω) :=
    TwinThmEW.map_mem_WSet hΩ.hyp (TwinEdge.hypOmegaGen_quotFamily_odd hΩ.hyp hN) hN d.hW
  rw [hW] at hmap
  obtain rfl : W₀.map πN = W := hmap
  obtain ⟨hXM, hsurj⟩ := d.index hD
  have hWE := d.W_eq hΩ hall hsurj
  refine ⟨?_, d.centralizer_eq hXM hsurj hWE⟩
  obtain ⟨e⟩ := d.nonempty_equiv_UV hΩ
  exact ⟨(AscQuot.quotRestrictEquiv (inf_oddCore_eq_bot d.hW2)).symm.trans
    ((MulEquiv.subgroupCongr hWE).trans e)⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.WR1
