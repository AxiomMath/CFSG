module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private theorem zs_le_normalizer_of_conj_mem {G : Type} [Group G] {H X : Subgroup G}
    (h : ∀ g ∈ H, ∀ x ∈ X, g * x * g⁻¹ ∈ X) : H ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (H.inv_mem hg) (g * x * g⁻¹) hx
  simpa [mul_assoc] using this

private theorem zs_conj_mem_closure {G : Type} [Group G] {H : Subgroup G} {T : Set G}
    (h : ∀ g ∈ H, ∀ x ∈ T, g * x * g⁻¹ ∈ T) {g : G} (hg : g ∈ H) {x : G}
    (hx : x ∈ Subgroup.closure T) : g * x * g⁻¹ ∈ Subgroup.closure T := by
  induction hx using Subgroup.closure_induction with
  | mem z hz => exact Subgroup.subset_closure (h g hg z hz)
  | one => simp
  | mul a b _ _ iha ihb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact (Subgroup.closure T).mul_mem iha ihb
  | inv a _ iha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact (Subgroup.closure T).inv_mem iha

private theorem zs_le_normalizer_omega1 {G : Type} [Group G] {H X : Subgroup G}
    (h : H ≤ Subgroup.normalizer (X : Set G)) :
    H ≤ Subgroup.normalizer ((dsOmega1 X : Subgroup G) : Set G) := by
  refine zs_le_normalizer_of_conj_mem fun g hg x hx => ?_
  refine zs_conj_mem_closure (H := H) (T := {y : G | y ∈ X ∧ y ^ 2 = 1}) ?_ hg hx
  rintro k hk y ⟨hyX, hy2⟩
  show k * y * k⁻¹ ∈ X ∧ (k * y * k⁻¹) ^ 2 = 1
  refine ⟨(Subgroup.mem_normalizer_iff.mp (h hk) y).mp hyX, ?_⟩
  have e : (k * y * k⁻¹) ^ 2 = k * y ^ 2 * k⁻¹ := by
    simp only [pow_two, mul_assoc, inv_mul_cancel_left]
  rw [e, hy2, mul_one, mul_inv_cancel]

private theorem zs_mem_centerOf_iff {G : Type} [Group G] {X : Subgroup G} {x : G} :
    x ∈ centerOf X ↔ x ∈ X ∧ ∀ y ∈ X, y * x = x * y := by
  simp only [centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

private theorem zs_le_normalizer_center {G : Type} [Group G] {H X : Subgroup G}
    (h : H ≤ Subgroup.normalizer (X : Set G)) :
    H ≤ Subgroup.normalizer ((centerOf X : Subgroup G) : Set G) := by
  refine zs_le_normalizer_of_conj_mem fun g hg x hx => ?_
  obtain ⟨hxX, hxc⟩ := zs_mem_centerOf_iff.mp hx
  refine zs_mem_centerOf_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp (h hg) x).mp hxX, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (h (H.inv_mem hg)) y).mp hy
    simpa using this
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hxc _ hy']
    _ = g * x * g⁻¹ * y := by group

private theorem zs_mem_dsOmega1 {G : Type} [Group G] {X : Subgroup G} {x : G}
    (hx : x ∈ X) (hx2 : x ^ 2 = 1) : x ∈ dsOmega1 X := by
  unfold dsOmega1
  exact Subgroup.subset_closure ⟨hx, hx2⟩

private theorem zs_dsOmega1_le {G : Type} [Group G] {X K : Subgroup G}
    (h : ∀ x ∈ X, x ^ 2 = 1 → x ∈ K) : dsOmega1 X ≤ K := by
  unfold dsOmega1
  exact (Subgroup.closure_le K).2 fun _ hx => h _ hx.1 hx.2

private theorem zs_conj_mem_dsConjClosure {G : Type} [Group G] {Y X : Subgroup G} {y z : G}
    (hy : y ∈ Y) (hz : z ∈ X) : y * z * y⁻¹ ∈ dsConjClosure Y X := by
  have hmem : y * z * y⁻¹ ∈ X.map (MulAut.conj y).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hle : X.map (MulAut.conj y).toMonoidHom ≤ dsConjClosure Y X :=
    le_iSup₂ (f := fun w (_ : w ∈ Y) => X.map (MulAut.conj w).toMonoidHom) y hy
  exact hle hmem

private theorem zs_dsConjClosure_le {G : Type} [Group G] {Y X K : Subgroup G}
    (h : ∀ y ∈ Y, ∀ z ∈ X, y * z * y⁻¹ ∈ K) : dsConjClosure Y X ≤ K := by
  unfold dsConjClosure
  refine iSup₂_le fun y hy => ?_
  rintro _ ⟨z, hz, rfl⟩
  exact h y hy z hz

private theorem zs_dsConjClosure_le_comap {G : Type} [Group G] {Y X : Subgroup G} {g : G}
    (h : ∀ y ∈ Y, ∀ z ∈ X, g * (y * z * y⁻¹) * g⁻¹ ∈ dsConjClosure Y X) :
    dsConjClosure Y X ≤ (dsConjClosure Y X).comap (MulAut.conj g).toMonoidHom :=
  zs_dsConjClosure_le fun y hy z hz => h y hy z hz

private theorem zs_le_normalizer_dsConjClosure {G : Type} [Group G] (Y X : Subgroup G) :
    Y ≤ Subgroup.normalizer ((dsConjClosure Y X : Subgroup G) : Set G) := by
  refine zs_le_normalizer_of_conj_mem fun y hy x hx => ?_
  have hstep : ∀ y' ∈ Y, ∀ z ∈ X, y * (y' * z * y'⁻¹) * y⁻¹ ∈ dsConjClosure Y X := by
    intro y' hy' z hz
    have e : y * (y' * z * y'⁻¹) * y⁻¹ = (y * y') * z * (y * y')⁻¹ := by group
    rw [e]
    exact zs_conj_mem_dsConjClosure (Y.mul_mem hy hy') hz
  have hle := zs_dsConjClosure_le_comap (Y := Y) (X := X) (g := y) hstep
  exact hle hx

private theorem zs_bigB_le_parabolic {G : Type} [Group G] (L1 L2 S : Subgroup G) :
    bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S :=
  le_sup_right

private theorem zs_S_le_bigB {G : Type} [Group G] (L1 L2 S : Subgroup G) :
    S ≤ bigB L1 L2 S := by
  unfold bigB
  exact le_sup_right

private theorem zs_bigB_le_normalizer_dsZ {G : Type} [Group G] {L1 L2 S : Subgroup G}
    (h : ZSetting L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer ((dsZ S : Subgroup G) : Set G) :=
  zs_le_normalizer_omega1 (zs_le_normalizer_center h.bnorm)

private theorem zs_S_ne_bot {G : Type} [Group G] {L1 L2 S : Subgroup G} (h : ZSetting L1 L2 S) :
    S ≠ ⊥ := by
  intro hS
  apply h.hyp.r1.borel_ne
  rw [hS, bot_inf_eq]
  refine inf_eq_left.2 ?_
  intro g _
  exact Subgroup.mem_normalizer_iff.mpr fun x => by simp

private theorem zs_dsZ_ne_bot {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) : dsZ S ≠ ⊥ := by
  intro hbot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS1
  have hZ : Nontrivial (Subgroup.center S) := hS2.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    rcases (hS2.to_subgroup (Subgroup.center S)).card_eq_or_dvd with hone | hdiv
    · exact absurd (Nat.card_eq_one_iff_unique.mp hone).1 (not_subsingleton _)
    · exact hdiv
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 2 hdvd
  have hc2 : c ^ 2 = 1 := by
    rw [← hc]
    exact pow_orderOf_eq_one c
  have hxZ : ((c : S) : G) ∈ centerOf S :=
    zs_mem_centerOf_iff.mpr ⟨(c : S).2, fun y hy => by
      have h1 := Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩
      exact congrArg Subtype.val h1⟩
  have hx2 : ((c : S) : G) ^ 2 = 1 := by
    have h1 := congrArg (fun t : Subgroup.center S => ((t : S) : G)) hc2
    simpa using h1
  have hxmem : ((c : S) : G) ∈ dsZ S := zs_mem_dsOmega1 hxZ hx2
  rw [hbot, Subgroup.mem_bot] at hxmem
  have hc1 : c = 1 := Subtype.ext (Subtype.ext hxmem)
  rw [hc1, orderOf_one] at hc
  norm_num at hc

private theorem zs_pow_two_of_mem_omega1 {G : Type} [Group G] {X : Subgroup G}
    (hc : ∀ a ∈ dsOmega1 X, ∀ b ∈ dsOmega1 X, a * b = b * a) {x : G} (hx : x ∈ dsOmega1 X) :
    x ^ 2 = 1 := by
  unfold dsOmega1 at hc hx
  induction hx using Subgroup.closure_induction with
  | mem z hz => exact hz.2
  | one => exact one_pow 2
  | mul a b ha hb iha ihb => rw [Commute.mul_pow (hc a ha b hb), iha, ihb, mul_one]
  | inv a _ iha => rw [inv_pow, iha, inv_one]

private theorem zs_omega1_centerOf_elemAbelian {G : Type} [Group G] (Q : Subgroup G) :
    IsElemAbelian 2 (dsOmega1 (centerOf Q)) := by
  have hWc : dsOmega1 (centerOf Q) ≤ centerOf Q := zs_dsOmega1_le fun x hx _ => hx
  have hcomm : ∀ a ∈ dsOmega1 (centerOf Q), ∀ b ∈ dsOmega1 (centerOf Q), a * b = b * a := by
    intro a ha b hb
    have hbQ : b ∈ Q := (zs_mem_centerOf_iff.mp (hWc hb)).1
    exact ((zs_mem_centerOf_iff.mp (hWc ha)).2 b hbQ).symm
  exact ⟨isMulCommutative_iff.2 fun a b => Subtype.ext (hcomm (a : G) a.2 (b : G) b.2),
    fun x hx => zs_pow_two_of_mem_omega1 hcomm hx⟩

private theorem zs_parabolic_le_normalizer_W {G : Type} [Group G] {L1 L2 S : Subgroup G} :
    L1 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer ((dsOmega1 (centerOf (dsQ L1 L2 S)) : Subgroup G) : Set G) :=
  zs_le_normalizer_omega1 (zs_le_normalizer_center
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L1 ⊔ bigB L1 L2 S)))

private theorem zs_dsZ_le_W {G : Type} [Group G] {L1 L2 S : Subgroup G} (h : ZSetting L1 L2 S)
    (hQS : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S) :
    dsZ S ≤ dsOmega1 (centerOf (dsQ L1 L2 S)) := by
  have hC : (L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.centralizer ((pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Subgroup G) : Set G) ≤
        pCoreOf 2 (L1 ⊔ bigB L1 L2 S) :=
    F1.parabolic_charTwo h.hyp
  have hSP : S ≤ L1 ⊔ bigB L1 L2 S :=
    (zs_S_le_bigB L1 L2 S).trans (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S)
  refine zs_dsOmega1_le (X := centerOf S) fun x hxS hx2 => zs_mem_dsOmega1 ?_ hx2
  obtain ⟨hxS', hxc⟩ := zs_mem_centerOf_iff.mp hxS
  have hcomm : ∀ q ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S), q * x = x * q :=
    fun q hq => hxc q (hQS hq)
  have hxQ : x ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) :=
    hC (Subgroup.mem_inf.mpr ⟨hSP hxS', Subgroup.mem_centralizer_iff.mpr hcomm⟩)
  exact zs_mem_centerOf_iff.mpr ⟨hxQ, hcomm⟩

private theorem zs_dsZi_le_W {G : Type} [Group G] {L1 L2 S : Subgroup G} (h : ZSetting L1 L2 S)
    (hQS : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S) :
    dsZi L1 S ≤ dsOmega1 (centerOf (dsQ L1 L2 S)) := by
  have hZW := zs_dsZ_le_W h hQS
  have hN : L1 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer ((dsOmega1 (centerOf (dsQ L1 L2 S)) : Subgroup G) : Set G) :=
    zs_parabolic_le_normalizer_W
  have hLP : L1 ≤ L1 ⊔ bigB L1 L2 S := le_sup_left
  refine zs_dsConjClosure_le (Y := L1) (X := dsZ S) fun y hy z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hN (hLP hy)) z).mp (hZW hz)

private theorem zs_parabolic_le_normalizer_dsZi {G : Type} [Group G] {L1 L2 S : Subgroup G}
    (h : ZSetting L1 L2 S) :
    L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer ((dsZi L1 S : Subgroup G) : Set G) := by
  have hBL1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (zs_bigB_le_parabolic L1 L2 S).trans (F1.parabolic_le_normalizer h.hyp)
  have hBZ := zs_bigB_le_normalizer_dsZ h
  have hkey : ∀ p ∈ L1 ⊔ bigB L1 L2 S, ∀ z ∈ dsZ S, p * z * p⁻¹ ∈ dsZi L1 S := by
    intro p hp z hz
    obtain ⟨l, hl, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBL1).mp hp
    have hbz : b * z * b⁻¹ ∈ dsZ S := (Subgroup.mem_normalizer_iff.mp (hBZ hb) z).mp hz
    have e : l * b * z * (l * b)⁻¹ = l * (b * z * b⁻¹) * l⁻¹ := by group
    rw [e]
    exact zs_conj_mem_dsConjClosure hl hbz
  refine sup_le (zs_le_normalizer_dsConjClosure L1 (dsZ S)) ?_
  refine zs_le_normalizer_of_conj_mem fun g hg x hx => ?_
  have hBP : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := le_sup_right
  have hLP : L1 ≤ L1 ⊔ bigB L1 L2 S := le_sup_left
  have hstep : ∀ y ∈ L1, ∀ z ∈ dsZ S, g * (y * z * y⁻¹) * g⁻¹ ∈ dsZi L1 S := by
    intro y hy z hz
    have e : g * (y * z * y⁻¹) * g⁻¹ = (g * y) * z * (g * y)⁻¹ := by group
    rw [e]
    exact hkey (g * y) ((L1 ⊔ bigB L1 L2 S).mul_mem (hBP hg) (hLP hy)) z hz
  have hle := zs_dsConjClosure_le_comap (Y := L1) (X := dsZ S) (g := g) hstep
  exact hle hx

theorem leafZiStructure [DSLeaf LeafSylowS] [DSLeaf LeafRankBounds] : LeafZiStructure := by
  intro G _ _ L1 L2 S h
  have hQS : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := (sylow_s h.hyp).2.2
  have hS2 : IsPGroup 2 S := h.hyp.hyp.h1.pgroup
  have hW : IsElemAbelian 2 (dsOmega1 (centerOf (dsQ L1 L2 S))) :=
    zs_omega1_centerOf_elemAbelian (dsQ L1 L2 S)
  exact ⟨zs_dsZ_ne_bot hS2 (zs_S_ne_bot h), dsZ_le_dsZi L1 S, zs_dsZi_le_W h hQS, hW,
    (rank_bounds (G := G)).2 _ hW, zs_parabolic_le_normalizer_dsZi h,
    zs_parabolic_le_normalizer_W⟩

end CFSG.GH74.QTGen4.DSGen4
