module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoBigMod
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoShape3Basic
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartTheta
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootOdd

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two

open Subgroup Equiv Equiv.Perm AltStdBal AltStdSec
open scoped Pointwise

structure Base (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ) (z : G) : Prop where
  std : StandardSetting G L
  hn : 8 ≤ n
  iso : Nonempty (L ≃* alternatingGroup (Fin n))
  cyc : Cyc L Q z
  card : Nat.card Q = 2

structure Shape (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ) (z u : G) : Prop
    extends Base G L Q n z where
  cent : u ∈ centralizer ({z} : Set G)
  outer : u ∉ L ⊔ centralizer (L : Set G)
  sq : u ^ 2 = 1

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z u : G}

theorem Base.of_orderTwo {θ : L ≃* alternatingGroup (Fin n)} (O : OrderTwo G L Q n θ z) :
    Base G L Q n z :=
  ⟨O.std, by have := O.hn; omega, ⟨θ⟩, O.cyc, O.card⟩

theorem Shape.of_orderTwo {θ : L ≃* alternatingGroup (Fin n)} (O : OrderTwo G L Q n θ z)
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ centralizer (L : Set G))
    (hu2 : u ^ 2 = 1) : Shape G L Q n z u :=
  ⟨Base.of_orderTwo O, hu, huL, hu2⟩

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers (z : G) :
    centralizer ({z} : Set G) ≤ normalizer (zpowers z : Set G) := by
  intro s hs
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  exact ((Commute.zpow_right (show Commute s z from mem_centralizer_singleton_iff.1 hs) k).eq).symm

section OddY

theorem oddY_le (d : Cyc L Q z) :
    oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) ≤
      centralizer (L : Set G) ⊓ centralizer ({z} : Set G) :=
  (oddPart_spec (cyc_le_inf_cent d) d.pgroup (cyc_odd_relIndex_inf d) d.cyclic).1

theorem oddY_le_centralizer (d : Cyc L Q z) :
    oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) ≤ centralizer (L : Set G) :=
  fun _ hy => (oddY_le d hy).1

theorem oddY_le_centralizer_z (d : Cyc L Q z) :
    oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) ≤ centralizer ({z} : Set G) :=
  fun _ hy => (oddY_le d hy).2

theorem odd_card_oddY (d : Cyc L Q z) :
    Odd (Nat.card (oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)))) :=
  (oddPart_spec (cyc_le_inf_cent d) d.pgroup (cyc_odd_relIndex_inf d) d.cyclic).2.2.1

theorem odd_orderOf_of_mem_oddY (d : Cyc L Q z) {y : G}
    (hy : y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G))) :
    Odd (orderOf y) := by
  have h1 := orderOf_dvd_natCard
    (⟨y, hy⟩ : oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)))
  rw [Subgroup.orderOf_mk] at h1
  exact Odd.of_dvd_nat (odd_card_oddY d) h1

theorem oddY_inf_zpowers (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) :
    oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) ⊓ zpowers z = ⊥ := by
  rw [← eq_zpowers_of_card_eq_two_of_cyc d hQ2]
  exact (oddPart_spec (cyc_le_inf_cent d) d.pgroup (cyc_odd_relIndex_inf d) d.cyclic).2.2.2.1

theorem exists_oddY_of_mem_inf (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {m : G}
    (hm : m ∈ centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) :
    ∃ y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)), m = y ∨ m = y * z := by
  obtain ⟨y, hy, q, hq, rfl⟩ :=
    (oddPart_spec (cyc_le_inf_cent d) d.pgroup (cyc_odd_relIndex_inf d) d.cyclic).2.2.2.2 m hm
  rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with rfl | rfl
  · exact ⟨y, hy, Or.inl (mul_one y)⟩
  · exact ⟨y, hy, Or.inr rfl⟩

theorem le_normalizer_oddY (hS : StandardSetting G L) (d : Cyc L Q z) :
    centralizer ({z} : Set G) ≤
      normalizer (oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro w
  refine ⟨fun hw => oddJunk_conj_mem hS d hc hw, fun hw => ?_⟩
  have := oddJunk_conj_mem hS d (inv_mem hc) hw
  simpa [mul_assoc] using this

end OddY

section Perm

@[expose] noncomputable def permOf (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n))
    {x : G} (hx : x ∈ centralizer ({z} : Set G)) : Perm (Fin n) :=
  rho θ B.hn ⟨x, cent_le_normalizer B.std B.cyc hx⟩

theorem permOf_mul (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n)) {x y : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hy : y ∈ centralizer ({z} : Set G))
    (hxy : x * y ∈ centralizer ({z} : Set G)) :
    permOf B θ hxy = permOf B θ hx * permOf B θ hy := by
  unfold permOf
  rw [← map_mul]
  rfl

theorem permOf_inv (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n)) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hx' : x⁻¹ ∈ centralizer ({z} : Set G)) :
    permOf B θ hx' = (permOf B θ hx)⁻¹ := by
  unfold permOf
  rw [← map_inv]
  rfl

theorem permOf_of_mem (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n)) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hxL : x ∈ L) :
    permOf B θ hx = ((θ ⟨x, hxL⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) :=
  rho_of_mem θ B.hn ⟨x, hxL⟩ (cent_le_normalizer B.std B.cyc hx)

theorem permOf_eq_one_iff (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n)) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) : permOf B θ hx = 1 ↔ x ∈ centralizer (L : Set G) :=
  rho_eq_one_iff θ B.hn _

theorem permOf_congr (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n)) {x y : G}
    (hxy : x = y) (hx : x ∈ centralizer ({z} : Set G)) (hy : y ∈ centralizer ({z} : Set G)) :
    permOf B θ hx = permOf B θ hy := by
  subst hxy
  rfl

theorem permOf_one (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n)) :
    permOf B θ (one_mem (centralizer ({z} : Set G))) = 1 :=
  (permOf_eq_one_iff B θ _).2 (one_mem _)

theorem permOf_eq_one_of_mem_oddY (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n))
    {y : G} (hy : y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)))
    (hyC : y ∈ centralizer ({z} : Set G)) : permOf B θ hyC = 1 :=
  (permOf_eq_one_iff B θ hyC).2 (oddY_le_centralizer B.cyc hy)

theorem permOf_conj_of_mem_oddY (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n))
    {x y : G} (hx : x ∈ centralizer ({z} : Set G))
    (hy : y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)))
    (hyx : y * x * y⁻¹ ∈ centralizer ({z} : Set G)) : permOf B θ hyx = permOf B θ hx := by
  have hyC := oddY_le_centralizer_z B.cyc hy
  rw [permOf_mul B θ (mul_mem hyC hx) (inv_mem hyC) hyx, permOf_mul B θ hyC hx (mul_mem hyC hx),
    permOf_inv B θ hyC (inv_mem hyC), permOf_eq_one_of_mem_oddY B θ hy hyC]
  group

theorem comm_of_mem_corr_of_permOf_fix (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n))
    {x : G} (hx : x ∈ centralizer ({z} : Set G)) {F : Finset (Fin n)}
    (hF : ∀ i ∈ F, permOf B θ hx i = i) {w : G} (hw : w ∈ corr (X := G) θ (altSub F)) :
    x * w = w * x := by
  obtain ⟨hwL, hwT⟩ := mem_corr.1 hw
  have hxN : x ∈ normalizer (L : Set G) := cent_le_normalizer B.std B.cyc hx
  have hxw : x * w * x⁻¹ ∈ L := (mem_normalizer_iff.1 hxN w).1 hwL
  have h1 := rho_conj_apply θ B.hn hxN ⟨w, hwL⟩ ⟨x * w * x⁻¹, hxw⟩ rfl
  have hfix : permOf B θ hx ∈ fixSub F := hF
  have h2 := comm_altSub_fixSub hwT hfix
  have h3 : (θ ⟨x * w * x⁻¹, hxw⟩ : alternatingGroup (Fin n)) = θ ⟨w, hwL⟩ := by
    apply Subtype.ext
    rw [← h1]
    change permOf B θ hx * _ * (permOf B θ hx)⁻¹ = _
    rw [← h2]
    simp
  have h4 := θ.injective h3
  have h5 : x * w * x⁻¹ = w := congrArg Subtype.val h4
  calc x * w = (x * w * x⁻¹) * x := by group
    _ = w * x := by rw [h5]

theorem mem_normalizer_corr_fixFin (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n))
    {a y : G} (ha : a ∈ centralizer ({z} : Set G)) (hy : y ∈ centralizer ({z} : Set G))
    (hay : y * a = a * y) :
    y ∈ normalizer (corr (X := G) θ (altSub (fixFin (permOf B θ ha))) : Set G) := by
  have hyN : y ∈ normalizer (L : Set G) := cent_le_normalizer B.std B.cyc hy
  refine mem_normalizer_corr θ B.hn hyN (mem_normalizer_altSub fun i => ?_)
  have hcomm : permOf B θ hy * permOf B θ ha = permOf B θ ha * permOf B θ hy := by
    rw [← permOf_mul B θ hy ha (mul_mem hy ha), ← permOf_mul B θ ha hy (mul_mem ha hy)]
    congr 1
  have h2 := congrArg (fun f : Perm (Fin n) => f i) hcomm
  simp only [Perm.mul_apply] at h2
  rw [mem_fixFin, mem_fixFin]
  change permOf B θ ha i = i ↔ permOf B θ ha (permOf B θ hy i) = permOf B θ hy i
  constructor
  · intro hi
    rw [← h2, hi]
  · intro hi
    have h3 : permOf B θ hy (permOf B θ ha i) = permOf B θ hy i := by rw [h2, hi]
    exact (permOf B θ hy).injective h3

end Perm

section Complement

omit [Finite G] in
theorem mem_or_mul_mem_of_mem_complement {u : G} (hu : u ∈ normalizer (L : Set G)) (hu2 : u ^ 2 = 1)
    {c : G} (hc : c ∈ L ⊔ zpowers u) : c ∈ L ∨ c * u ∈ L := by
  obtain ⟨l, hl, w, hw, rfl⟩ := (mem_sup_zpowers_iff_of_mem_normalizer hu).1 hc
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul]
    simpa [hu2] using hl
  · right
    rw [zpow_add, zpow_mul, zpow_one]
    have hu1 : u * u = 1 := by rw [← pow_two, hu2]
    simpa [hu2, mul_assoc, hu1] using hl

theorem Shape.mem_normalizer (T : Shape G L Q n z u) : u ∈ normalizer (L : Set G) :=
  cent_le_normalizer T.std T.cyc T.cent

theorem Shape.le_normalizer (T : Shape G L Q n z u) : L ⊔ zpowers u ≤ normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer (zpowers_le.2 T.mem_normalizer)

theorem Shape.le_centralizer (T : Shape G L Q n z u) :
    L ⊔ zpowers u ≤ centralizer ({z} : Set G) :=
  sup_le (le_cent_single T.std T.cyc) (zpowers_le.2 T.cent)

theorem Shape.z_notMem (T : Shape G L Q n z u) : z ∉ L ⊔ zpowers u := by
  obtain ⟨θ⟩ := T.iso
  intro hz
  have hzK : z ∈ centralizer (L : Set G) := T.cyc.le T.cyc.mem
  rcases mem_or_mul_mem_of_mem_complement T.mem_normalizer T.sq hz with h1 | h1
  · have h2 := eq_one_of_mem_of_mem_centralizer θ (by have := T.hn; omega) h1 hzK
    have h3 := T.cyc.order
    rw [h2, orderOf_one] at h3
    omega
  · apply T.outer
    have : u = z⁻¹ * (z * u) := by group
    rw [this]
    exact mul_mem (mem_sup_right (inv_mem hzK)) (mem_sup_left h1)

theorem Shape.zpowers_inf (T : Shape G L Q n z u) : zpowers z ⊓ (L ⊔ zpowers u) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxz, hxS⟩
  have hxQ : x ∈ Q := by rw [eq_zpowers_of_card_eq_two_of_cyc T.cyc T.card]; exact hxz
  rcases eq_one_or_eq_of_card_eq_two T.cyc T.card hxQ with rfl | rfl
  · exact one_mem _
  · exact absurd hxS T.z_notMem

theorem Shape.mul_self_mem (T : Shape G L Q n z u) {x : G} (hx : x ∈ L ⊔ zpowers u) :
    x * x ∈ L := by
  rcases mem_or_mul_mem_of_mem_complement T.mem_normalizer T.sq hx with h1 | h1
  · exact mul_mem h1 h1
  · have hu1 : u * u = 1 := by rw [← pow_two, T.sq]
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu1
    have hux : u * (x * u) * u⁻¹ ∈ L := (mem_normalizer_iff.1 T.mem_normalizer _).1 h1
    rw [hu'] at hux
    have : x * x = (x * u) * (u * (x * u) * u) := by
      calc x * x = x * (u * u) * x * (u * u) := by rw [hu1]; group
        _ = (x * u) * (u * (x * u) * u) := by group
    rw [this]
    exact mul_mem h1 hux

@[expose] noncomputable def rhoSwap (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n)) :
    (L ⊔ zpowers u : Subgroup G) →* Perm (Fin n) :=
  (rho θ T.hn).comp (Subgroup.inclusion T.le_normalizer)

theorem rhoSwap_apply (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (s : (L ⊔ zpowers u : Subgroup G)) :
    rhoSwap T θ s = permOf T.toBase θ (T.le_centralizer s.2) := rfl

theorem rhoSwap_bijective (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n)) :
    Function.Bijective (rhoSwap T θ) := by
  have huN := T.mem_normalizer
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, rhoSwap_apply] at hs
    have hK := (permOf_eq_one_iff T.toBase θ _).1 hs
    rcases mem_or_mul_mem_of_mem_complement huN T.sq s.2 with h1 | h1
    · exact Subtype.ext (eq_one_of_mem_of_mem_centralizer θ (by have := T.hn; omega) h1 hK)
    · exfalso
      apply T.outer
      have : u = (s : G)⁻¹ * ((s : G) * u) := by group
      rw [this]
      exact mul_mem (mem_sup_right (inv_mem hK)) (mem_sup_left h1)
  · intro σ
    have hodd : sign (rho θ T.hn ⟨u, huN⟩) = -1 :=
      Shape3.sign_rho_eq_neg_one θ T.hn huN T.outer
    rcases Int.units_eq_one_or (sign σ) with hσ | hσ
    · have hmem : σ ∈ alternatingGroup (Fin n) := mem_alternatingGroup.2 hσ
      let l : L := θ.symm ⟨σ, hmem⟩
      refine ⟨⟨l, mem_sup_left l.2⟩, ?_⟩
      rw [rhoSwap_apply, permOf_of_mem T.toBase θ _ l.2]
      simp [l]
    · have hmem : σ * (rho θ T.hn ⟨u, huN⟩)⁻¹ ∈ alternatingGroup (Fin n) := by
        rw [mem_alternatingGroup, map_mul, map_inv, hσ, hodd]
        decide
      let l : L := θ.symm ⟨σ * (rho θ T.hn ⟨u, huN⟩)⁻¹, hmem⟩
      have hlN : (l : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer l.2
      have hρl : rho θ T.hn ⟨l, hlN⟩ = σ * (rho θ T.hn ⟨u, huN⟩)⁻¹ := by
        rw [rho_of_mem θ T.hn l hlN]
        simp [l]
      refine ⟨⟨(l : G) * u, mul_mem (mem_sup_left l.2) (mem_sup_right (mem_zpowers u))⟩, ?_⟩
      show rho θ T.hn ⟨(l : G) * u, _⟩ = σ
      have : (⟨(l : G) * u, T.le_normalizer (mul_mem (mem_sup_left l.2)
          (mem_sup_right (mem_zpowers u)))⟩ : normalizer (L : Set G)) =
          ⟨l, hlN⟩ * ⟨u, huN⟩ := rfl
      rw [this, map_mul, hρl, inv_mul_cancel_right]

@[expose] noncomputable def swapIota (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n)) :
    Perm (Fin n) ≃* ↥(L ⊔ zpowers u) :=
  (MulEquiv.ofBijective (rhoSwap T θ) (rhoSwap_bijective T θ)).symm

theorem rhoSwap_swapIota (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (σ : Perm (Fin n)) : rhoSwap T θ (swapIota T θ σ) = σ :=
  (MulEquiv.ofBijective (rhoSwap T θ) (rhoSwap_bijective T θ)).apply_symm_apply σ

theorem swapIota_rhoSwap (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (s : ↥(L ⊔ zpowers u)) : swapIota T θ (rhoSwap T θ s) = s :=
  (MulEquiv.ofBijective (rhoSwap T θ) (rhoSwap_bijective T θ)).symm_apply_apply s

theorem swapIota_mem_centralizer (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (σ : Perm (Fin n)) :
    ((swapIota T θ σ : ↥(L ⊔ zpowers u)) : G) ∈ centralizer ({z} : Set G) :=
  T.le_centralizer (swapIota T θ σ).2

theorem permOf_swapIota (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (σ : Perm (Fin n)) : permOf T.toBase θ (swapIota_mem_centralizer T θ σ) = σ :=
  rhoSwap_swapIota T θ σ

theorem swapIota_comm_z (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (σ : Perm (Fin n)) : z * (swapIota T θ σ : G) = (swapIota T θ σ : G) * z :=
  (mem_centralizer_singleton_iff.1 (swapIota_mem_centralizer T θ σ)).symm

theorem swapIota_mul_self (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {σ : Perm (Fin n)} (hσ : σ * σ = 1) :
    (swapIota T θ σ : G) * (swapIota T θ σ : G) = 1 := by
  have : swapIota T θ σ * swapIota T θ σ = 1 := by rw [← map_mul, hσ, map_one]
  exact congrArg Subtype.val this

end Complement

section ModY

theorem exists_oddY_mul_swapIota (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {x : G} (hx : x ∈ centralizer ({z} : Set G)) :
    ∃ y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)),
      x = y * (swapIota T θ (permOf T.toBase θ hx) : G) ∨
        x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) := by
  have hsC := swapIota_mem_centralizer T θ (permOf T.toBase θ hx)
  have hps := permOf_swapIota T θ (permOf T.toBase θ hx)
  have hinv := inv_mem hsC
  have hxs := mul_mem hx hinv
  have hp1 : permOf T.toBase θ hxs = 1 := by
    rw [permOf_mul T.toBase θ hx hinv hxs, permOf_inv T.toBase θ hsC hinv, hps, mul_inv_cancel]
  have hK := (permOf_eq_one_iff T.toBase θ hxs).1 hp1
  obtain ⟨y, hy, h | h⟩ := exists_oddY_of_mem_inf T.cyc T.card ⟨hK, hxs⟩
  · refine ⟨y, hy, Or.inl ?_⟩
    rw [← h]
    group
  · refine ⟨y, hy, Or.inr ?_⟩
    rw [← mul_assoc, ← h]
    group

theorem exists_oddY_conj_swapIota (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {x : G} (hx : x ∈ centralizer ({z} : Set G)) (hx2 : x * x = 1) :
    ∃ y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)),
      x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
        x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹ := by
  have hsC := swapIota_mem_centralizer T θ (permOf T.toBase θ hx)
  have hσ2 : permOf T.toBase θ hx * permOf T.toBase θ hx = 1 := by
    rw [← permOf_mul T.toBase θ hx hx (mul_mem hx hx),
      permOf_congr T.toBase θ hx2 (mul_mem hx hx) (one_mem _), permOf_one]
  have hss := swapIota_mul_self T θ hσ2
  have hzs := swapIota_comm_z T θ (permOf T.toBase θ hx)
  have hz2 : z * z = 1 := T.cyc.mul_self
  have key : ∀ t : G, t ∈ centralizer ({z} : Set G) → t * t = 1 →
      ∀ y₀ ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)), x = y₀ * t →
        ∃ y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)),
          x = y * t * y⁻¹ := by
    intro t htC ht2 y₀ hy₀ hxt
    have htx : t * x ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) := by
      have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      have h1 := oddJunk_conj_mem T.std T.cyc htC hy₀
      rw [ht1] at h1
      rw [hxt, ← mul_assoc]
      exact h1
    obtain ⟨r, hr, hrx⟩ := exists_conj_of_involutions_of_mul_mem
      (fun w hw => odd_orderOf_of_mem_oddY T.cyc hw) hx2 ht2 htx
    refine ⟨r⁻¹, inv_mem hr, ?_⟩
    rw [inv_inv, ← hrx]
    group
  obtain ⟨y₀, hy₀, h | h⟩ := exists_oddY_mul_swapIota T θ hx
  · obtain ⟨y, hy, hyx⟩ := key _ hsC hss y₀ hy₀ h
    exact ⟨y, hy, Or.inl hyx⟩
  · have hzsC := mul_mem (mem_centralizer_singleton_iff.2 rfl : z ∈ centralizer ({z} : Set G)) hsC
    have hzs2 : z * (swapIota T θ (permOf T.toBase θ hx) : G) *
        (z * (swapIota T θ (permOf T.toBase θ hx) : G)) = 1 := by
      calc z * (swapIota T θ (permOf T.toBase θ hx) : G) *
            (z * (swapIota T θ (permOf T.toBase θ hx) : G)) =
          z * ((swapIota T θ (permOf T.toBase θ hx) : G) * z) *
            (swapIota T θ (permOf T.toBase θ hx) : G) := by group
        _ = z * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) *
            (swapIota T θ (permOf T.toBase θ hx) : G) := by rw [hzs]
        _ = (z * z) * ((swapIota T θ (permOf T.toBase θ hx) : G) *
            (swapIota T θ (permOf T.toBase θ hx) : G)) := by group
        _ = 1 := by rw [hz2, hss, one_mul]
    obtain ⟨y, hy, hyx⟩ := key _ hzsC hzs2 y₀ hy₀ h
    exact ⟨y, hy, Or.inr hyx⟩

theorem Shape.complement_le (T : Shape G L Q n z u) :
    zpowers z ⊔ (L ⊔ zpowers u) ≤ centralizer ({z} : Set G) :=
  sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)) T.le_centralizer

theorem centralizer_eq_sup_oddY (T : Shape G L Q n z u) :
    centralizer ({z} : Set G) =
      oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) ⊔
        (zpowers z ⊔ (L ⊔ zpowers u)) := by
  obtain ⟨θ⟩ := T.iso
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, h | h⟩ := exists_oddY_mul_swapIota T θ hx
    · rw [h]
      exact mul_mem (mem_sup_left hy)
        (mem_sup_right (mem_sup_right (swapIota T θ (permOf T.toBase θ hx)).2))
    · rw [h]
      exact mul_mem (mem_sup_left hy) (mem_sup_right (mul_mem (mem_sup_left (mem_zpowers z))
        (mem_sup_right (swapIota T θ (permOf T.toBase θ hx)).2)))
  · exact sup_le (oddY_le_centralizer_z T.cyc) T.complement_le

theorem oddY_inf_complement (T : Shape G L Q n z u) :
    oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) ⊓
      (zpowers z ⊔ (L ⊔ zpowers u)) = ⊥ := by
  obtain ⟨θ⟩ := T.iso
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwY, hwH⟩ := Subgroup.mem_inf.1 hw
  have hSN : L ⊔ zpowers u ≤ normalizer (zpowers z : Set G) :=
    T.le_centralizer.trans (centralizer_le_normalizer_zpowers z)
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left (zpowers z) (L ⊔ zpowers u) hSN
  have hw' : w ∈ (zpowers z : Set G) * ((L ⊔ zpowers u : Subgroup G) : Set G) := by
    rw [← hset]
    exact hwH
  obtain ⟨q, hq, s, hs, rfl⟩ := Set.mem_mul.1 hw'
  have hqQ : q ∈ Q := by rw [eq_zpowers_of_card_eq_two_of_cyc T.cyc T.card]; exact hq
  have hqK : q ∈ centralizer (L : Set G) := T.cyc.le hqQ
  have hwK : q * s ∈ centralizer (L : Set G) := oddY_le_centralizer T.cyc hwY
  have hsK : s ∈ centralizer (L : Set G) := by
    have : s = q⁻¹ * (q * s) := by group
    rw [this]
    exact mul_mem (inv_mem hqK) hwK
  have hs1 : s = 1 := by
    have h1 : rhoSwap T θ ⟨s, hs⟩ = 1 := by
      rw [rhoSwap_apply]
      exact (permOf_eq_one_iff T.toBase θ _).2 hsK
    have h2 := (rhoSwap_bijective T θ).1 (h1.trans (map_one _).symm)
    exact congrArg Subtype.val h2
  rw [hs1, mul_one] at hwY ⊢
  have : q ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) ⊓ zpowers z :=
    ⟨hwY, hq⟩
  rw [oddY_inf_zpowers T.cyc T.card] at this
  exact this

theorem card_complement_eq (T : Shape G L Q n z u) :
    Nat.card (zpowers z ⊔ (L ⊔ zpowers u) : Subgroup G) = 2 * n.factorial := by
  obtain ⟨θ⟩ := T.iso
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (zpowers z)
      (L ⊔ zpowers u) (T.le_centralizer.trans (centralizer_le_normalizer_zpowers z))
      (disjoint_iff.2 T.zpowers_inf),
    Nat.card_zpowers, T.cyc.order, Nat.card_congr (swapIota T θ).toEquiv.symm,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem card_centralizer_eq (T : Shape G L Q n z u) :
    Nat.card (centralizer ({z} : Set G)) =
      Nat.card (oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G))) *
        (2 * n.factorial) := by
  have hHN : zpowers z ⊔ (L ⊔ zpowers u) ≤
      normalizer (oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) : Set G) :=
    T.complement_le.trans (le_normalizer_oddY T.std T.cyc)
  calc Nat.card (centralizer ({z} : Set G)) =
      Nat.card (oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) ⊔
        (zpowers z ⊔ (L ⊔ zpowers u)) : Subgroup G) := by
        rw [← centralizer_eq_sup_oddY T]
    _ = Nat.card (oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G))) *
        Nat.card (zpowers z ⊔ (L ⊔ zpowers u) : Subgroup G) :=
        CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hHN
          (disjoint_iff.2 (oddY_inf_complement T))
    _ = _ := by rw [card_complement_eq T]

theorem mul_self_mem_sup_oddY (T : Shape G L Q n z u) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) :
    x * x ∈ L ⊔ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) := by
  obtain ⟨θ⟩ := T.iso
  have hsS := (swapIota T θ (permOf T.toBase θ hx)).2
  have hsC := swapIota_mem_centralizer T θ (permOf T.toBase θ hx)
  have hss := T.mul_self_mem hsS
  have hzs := swapIota_comm_z T θ (permOf T.toBase θ hx)
  have hz2 : z * z = 1 := T.cyc.mul_self
  have key : ∀ t : G, t ∈ centralizer ({z} : Set G) → t * t ∈ L →
      ∀ y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)), x = y * t →
        x * x ∈ L ⊔ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) := by
    intro t htC htt y hy hxt
    have hy' := oddJunk_conj_mem T.std T.cyc htC hy
    have : x * x = (y * (t * y * t⁻¹)) * (t * t) := by rw [hxt]; group
    rw [this]
    exact mul_mem (mem_sup_right (mul_mem hy hy')) (mem_sup_left htt)
  obtain ⟨y, hy, h | h⟩ := exists_oddY_mul_swapIota T θ hx
  · exact key _ hsC hss y hy h
  · refine key _ (mul_mem (mem_centralizer_singleton_iff.2 rfl) hsC) ?_ y hy h
    have : z * (swapIota T θ (permOf T.toBase θ hx) : G) *
        (z * (swapIota T θ (permOf T.toBase θ hx) : G)) =
        (swapIota T θ (permOf T.toBase θ hx) : G) *
          (swapIota T θ (permOf T.toBase θ hx) : G) := by
      calc z * (swapIota T θ (permOf T.toBase θ hx) : G) *
            (z * (swapIota T θ (permOf T.toBase θ hx) : G)) =
          z * ((swapIota T θ (permOf T.toBase θ hx) : G) * z) *
            (swapIota T θ (permOf T.toBase θ hx) : G) := by group
        _ = z * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) *
            (swapIota T θ (permOf T.toBase θ hx) : G) := by rw [hzs]
        _ = (z * z) * ((swapIota T θ (permOf T.toBase θ hx) : G) *
            (swapIota T θ (permOf T.toBase θ hx) : G)) := by group
        _ = _ := by rw [hz2, one_mul]
    rw [this]
    exact hss

theorem mem_sup_oddY_of_odd (T : Shape G L Q n z u) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hodd : Odd (orderOf x)) :
    x ∈ L ⊔ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have h2 : x = (x * x) ^ (k + 1) := by
    calc x = x ^ (2 * k + 1) * x := by rw [h1, one_mul]
      _ = x ^ (2 * (k + 1)) := by rw [← pow_succ]; congr 1
      _ = (x * x) ^ (k + 1) := by rw [pow_mul, pow_two]
  rw [h2]
  exact pow_mem (mul_self_mem_sup_oddY T hx) (k + 1)

theorem exists_lift_commuting (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {a' : G} (ha' : a' ∈ centralizer ({z} : Set G)) (ha'2 : a' * a' = 1) {c : Perm (Fin n)}
    (hc : c * permOf T.toBase θ ha' = permOf T.toBase θ ha' * c) :
    ∃ (s : G) (hs : s ∈ centralizer ({z} : Set G)), permOf T.toBase θ hs = c ∧ s * a' = a' * s := by
  obtain ⟨y, hy, hya⟩ := exists_oddY_conj_swapIota T θ ha' ha'2
  have hwC := swapIota_mem_centralizer T θ c
  have hws : (swapIota T θ c : G) * (swapIota T θ (permOf T.toBase θ ha') : G) =
      (swapIota T θ (permOf T.toBase θ ha') : G) * (swapIota T θ c : G) := by
    have : swapIota T θ c * swapIota T θ (permOf T.toBase θ ha') =
        swapIota T θ (permOf T.toBase θ ha') * swapIota T θ c := by
      rw [← map_mul, ← map_mul, hc]
    exact congrArg Subtype.val this
  have hwz := (swapIota_comm_z T θ c).symm
  have hyC := oddY_le_centralizer_z T.cyc hy
  have hyw := mul_mem hyC hwC
  have hsC := mul_mem hyw (inv_mem hyC)
  refine ⟨_, hsC, ?_, ?_⟩
  · rw [permOf_mul T.toBase θ hyw (inv_mem hyC) hsC, permOf_mul T.toBase θ hyC hwC hyw,
      permOf_inv T.toBase θ hyC (inv_mem hyC), permOf_eq_one_of_mem_oddY T.toBase θ hy hyC,
      permOf_swapIota]
    group
  · have key : ∀ t : G, (swapIota T θ c : G) * t = t * (swapIota T θ c : G) →
        a' = y * t * y⁻¹ →
          y * (swapIota T θ c : G) * y⁻¹ * a' = a' * (y * (swapIota T θ c : G) * y⁻¹) := by
      intro t hwt hat
      rw [hat]
      calc y * (swapIota T θ c : G) * y⁻¹ * (y * t * y⁻¹) =
          y * ((swapIota T θ c : G) * t) * y⁻¹ := by group
        _ = y * (t * (swapIota T θ c : G)) * y⁻¹ := by rw [hwt]
        _ = y * t * y⁻¹ * (y * (swapIota T θ c : G) * y⁻¹) := by group
    rcases hya with h | h
    · exact key _ hws h
    · refine key _ ?_ h
      calc (swapIota T θ c : G) * (z * (swapIota T θ (permOf T.toBase θ ha') : G)) =
          ((swapIota T θ c : G) * z) * (swapIota T θ (permOf T.toBase θ ha') : G) := by group
        _ = (z * (swapIota T θ c : G)) * (swapIota T θ (permOf T.toBase θ ha') : G) := by
          rw [hwz]
        _ = z * ((swapIota T θ c : G) * (swapIota T θ (permOf T.toBase θ ha') : G)) := by group
        _ = z * ((swapIota T θ (permOf T.toBase θ ha') : G) * (swapIota T θ c : G)) := by
          rw [hws]
        _ = z * (swapIota T θ (permOf T.toBase θ ha') : G) * (swapIota T θ c : G) := by group

end ModY

section Kappa

@[expose] noncomputable def kappa (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (S : Finset (Fin n)) : Perm ↥Sᶜ →* G :=
  (L ⊔ zpowers u).subtype.comp
    ((swapIota T θ).toMonoidHom.comp (Perm.ofSubtype : Perm ↥Sᶜ →* Perm (Fin n)))

theorem kappa_apply (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (S : Finset (Fin n)) (π : Perm ↥Sᶜ) :
    kappa T θ S π = ((swapIota T θ (Perm.ofSubtype π) : ↥(L ⊔ zpowers u)) : G) := rfl

theorem kappa_mem_centralizer (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (S : Finset (Fin n)) (π : Perm ↥Sᶜ) : kappa T θ S π ∈ centralizer ({z} : Set G) :=
  swapIota_mem_centralizer T θ _

theorem permOf_kappa (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (S : Finset (Fin n)) (π : Perm ↥Sᶜ) :
    permOf T.toBase θ (kappa_mem_centralizer T θ S π) = Perm.ofSubtype π :=
  permOf_swapIota T θ _

theorem kappa_injective (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (S : Finset (Fin n)) : Function.Injective (kappa T θ S) := by
  intro π₁ π₂ h12
  have h1 : swapIota T θ (Perm.ofSubtype π₁) = swapIota T θ (Perm.ofSubtype π₂) := Subtype.ext h12
  exact Perm.ofSubtype_injective ((swapIota T θ).injective h1)

theorem kappa_mem_centralizer_root (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (S : Finset (Fin n)) (π : Perm ↥Sᶜ) :
    kappa T θ S π ∈ centralizer (corr (X := G) θ (altSub S) : Set G) := by
  rw [mem_centralizer_iff]
  intro r hr
  refine (comm_of_mem_corr_of_permOf_fix T.toBase θ (kappa_mem_centralizer T θ S π)
    (F := S) (fun i hi => ?_) hr).symm
  rw [permOf_kappa]
  exact Perm.ofSubtype_apply_of_not_mem π (by simpa using hi)

theorem kappa_sq_mem_corr (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (S : Finset (Fin n)) (π : Perm ↥Sᶜ) :
    kappa T θ S π * kappa T θ S π ∈ corr (X := G) θ (altSub Sᶜ) := by
  have hC := kappa_mem_centralizer T θ S π
  have hL : kappa T θ S π * kappa T θ S π ∈ L :=
    T.mul_self_mem (swapIota T θ (Perm.ofSubtype π)).2
  refine mem_corr.2 ⟨hL, ?_⟩
  have h1 := permOf_of_mem T.toBase θ (mul_mem hC hC) hL
  rw [permOf_mul T.toBase θ hC hC (mul_mem hC hC), permOf_kappa] at h1
  rw [← h1]
  refine mem_altSub.2 ⟨?_, fun i hi => ?_⟩
  · rw [Perm.sign_mul, Int.units_mul_self]
  · have hiS : i ∈ S := by simpa using hi
    have : Perm.ofSubtype π i = i := Perm.ofSubtype_apply_of_not_mem π (by simpa using hiS)
    simp [Perm.mul_apply, this]

@[expose] noncomputable def thetaHom (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (S : Finset (Fin n)) : Perm ↥Sᶜ →* Sec G (corr (X := G) θ (altSub S)) :=
  (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (corr (X := G) θ (altSub S) : Set G)))).comp
    ((kappa T θ S).codRestrict (centralizer (corr (X := G) θ (altSub S) : Set G))
      (kappa_mem_centralizer_root T θ S))

theorem thetaHom_apply (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (S : Finset (Fin n)) (π : Perm ↥Sᶜ) :
    thetaHom T θ S π =
      (QuotientGroup.mk ⟨kappa T θ S π, kappa_mem_centralizer_root T θ S π⟩ :
        Sec G (corr (X := G) θ (altSub S))) := rfl

theorem thetaHom_injective (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {S : Finset (Fin n)} (hSc : 5 ≤ Sᶜ.card) : Function.Injective (thetaHom T θ S) := by
  rw [injective_iff_map_eq_one]
  intro π hπ
  rw [thetaHom_apply] at hπ
  have hO := (QuotientGroup.eq_one_iff _).1 hπ
  have hCR := kappa_mem_centralizer_root T θ S π
  have hsqO : (⟨kappa T θ S π, hCR⟩ : ↥(centralizer (corr (X := G) θ (altSub S) : Set G))) *
      ⟨kappa T θ S π, hCR⟩ ∈ CFSG.oddCore ↥(centralizer (corr (X := G) θ (altSub S) : Set G)) :=
    mul_mem hO hO
  have hsq1 := oddCore_inf_corr_compl θ hSc _ (kappa_sq_mem_corr T θ S π) hsqO
  have hsq : kappa T θ S π * kappa T θ S π = 1 := congrArg Subtype.val hsq1
  have hodd : Odd (orderOf (kappa T θ S π)) := by
    have := orderOf_odd_of_mem_oddCore hO
    rwa [Subgroup.orderOf_mk] at this
  have hdvd : orderOf (kappa T θ S π) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have h1 : orderOf (kappa T θ S π) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact h1
    · rw [h2] at hodd; exact absurd hodd (by decide)
  have h2 : kappa T θ S π = 1 := orderOf_eq_one_iff.1 h1
  exact kappa_injective T θ S (by rw [h2, map_one])

theorem thetaHom_comm_z (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (S : Finset (Fin n)) (hz : z ∈ centralizer (corr (X := G) θ (altSub S) : Set G))
    (π : Perm ↥Sᶜ) :
    thetaHom T θ S π * (QuotientGroup.mk ⟨z, hz⟩ : Sec G (corr (X := G) θ (altSub S))) =
      QuotientGroup.mk ⟨z, hz⟩ * thetaHom T θ S π := by
  rw [thetaHom_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.1 (kappa_mem_centralizer T θ S π))

theorem thetaHom_ne_z (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (S : Finset (Fin n)) (hz : z ∈ centralizer (corr (X := G) θ (altSub S) : Set G))
    (π : Perm ↥Sᶜ) :
    thetaHom T θ S π ≠ (QuotientGroup.mk ⟨z, hz⟩ : Sec G (corr (X := G) θ (altSub S))) := by
  intro hπ
  rw [thetaHom_apply, QuotientGroup.eq] at hπ
  have hodd0 := orderOf_odd_of_mem_oddCore hπ
  rw [Subgroup.orderOf_mk] at hodd0
  have hxz : kappa T θ S π * z = z * kappa T θ S π :=
    mem_centralizer_singleton_iff.1 (kappa_mem_centralizer T θ S π)
  have hz2 : z * z = 1 := T.cyc.mul_self
  obtain ⟨r, hr⟩ := hodd0
  have hpow : ((kappa T θ S π)⁻¹ * z) ^ (2 * r + 1) = 1 := by
    rw [← hr]; exact pow_orderOf_eq_one _
  have hcomm : Commute (kappa T θ S π)⁻¹ z :=
    Commute.inv_left (show Commute (kappa T θ S π) z from hxz)
  have hzpow : z ^ (2 * r + 1) = z := by
    rw [pow_succ, pow_mul, pow_two, hz2, one_pow, one_mul]
  rw [hcomm.mul_pow, hzpow, inv_pow] at hpow
  have hzx : z = kappa T θ S π ^ (2 * r + 1) := (inv_mul_eq_one.1 hpow).symm
  apply T.z_notMem
  rw [hzx]
  exact pow_mem (swapIota T θ (Perm.ofSubtype π)).2 _

end Kappa

end CFSG.OddStandard.AltStdCycTwo.Two
