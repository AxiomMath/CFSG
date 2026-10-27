module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltRec1
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltRec3
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatCongr
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatRecog
import CFSG.CGT.PushingUpLit.BHSSym.Delta

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUp

variable {V : Type} [CommGroup V]

theorem natural_of_fixed [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {M : ℕ} (hM : Odd M) (hM5 : 5 ≤ M)
    {L : Subgroup (MulAut V)} (θ : L ≃* alternatingGroup (Fin M))
    (hC : ∀ w : V, (∀ x : L, (x : MulAut V) w = w) → w = 1) (b : Fin M) {v : V} (hv : v ≠ 1)
    (hJ : ∀ x : L, θ x ∈ altStabilizer M {b} → (x : MulAut V) v = v)
    (hcard : Nat.card V = 2 ^ (M - 1)) (hVL : commV L = ⊤) :
    IsNatSectionWith (altAct M) θ (commV L) ⊥ := by
  obtain ⟨a, rfl⟩ := hM
  have hnat := natRecog_holds V hV L a (by omega) θ hC b v hv hJ
  have horb : orbitSpan L v = ⊤ := by
    obtain ⟨-, β, hβs, hβk, -⟩ := id hnat
    have hinj : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩), hcard,
      CFSG.CGT.PushingUpLit.BHSSym.card_coreMod_succ (2 * a)]
    rfl
  rw [hVL, ← horb]
  exact hnat

private theorem nrr_commV_map_conj (H : Subgroup (MulAut V)) (g : MulAut V) :
    commV (H.map (MulAut.conj g).toMonoidHom) = (commV H).map g.toMonoidHom :=
  CFSG.Quasithin.commV_map_conj_eq H g

theorem card_commV_of_conj_threeCycle {k : ℕ} (hk : 3 ≤ k) {K : Subgroup (MulAut V)}
    (θ : K ≃* alternatingGroup (Fin k)) (h : IsNatSectionWith (altAct k) θ (commV K) ⊥)
    (hsplit : commV K ⊔ fixV K = ⊤) {y' g x : MulAut V} (hy' : y' ∈ K)
    (h3 : ((θ ⟨y', hy'⟩ : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)).IsThreeCycle)
    (hx : x = g * y' * g⁻¹) : Nat.card ↥(commV (Subgroup.zpowers x)) = 4 := by
  have hz : Subgroup.zpowers x = (Subgroup.zpowers y').map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_zpowers, hx]
    rfl
  rw [hz, nrr_commV_map_conj, Subgroup.card_map_of_injective g.injective]
  exact card_commV_threeCycle hk θ h hsplit hy' h3

private theorem nrr_card_mul [Finite V] {A B : Subgroup V} (hAB : A ⊓ B = ⊥) (hsup : A ⊔ B = ⊤) :
    Nat.card A * Nat.card B = Nat.card V := by
  have : B.Normal := Subgroup.normal_of_isMulCommutative B
  refine (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hAB)
    ?_).card_mul_card
  rw [← Subgroup.mul_normal, hsup]
  rfl

private theorem nrr_fixed_sup {K : Subgroup (MulAut V)} {x : MulAut V} {v : V}
    (hv : v ∈ fixV K) (hxv : (x⁻¹ : MulAut V) v ∈ fixV K) :
    ∀ z ∈ K ⊔ K.map (MulAut.conj x).toMonoidHom, z v = v := by
  have h : K ⊔ K.map (MulAut.conj x).toMonoidHom ≤ MulAction.stabilizer (MulAut V) v := by
    refine sup_le (fun y hy => ?_) ?_
    · exact MulAction.mem_stabilizer_iff.mpr (mem_fixV.mp hv y hy)
    · rintro _ ⟨y, hy, rfl⟩
      refine MulAction.mem_stabilizer_iff.mpr ?_
      show (x * y * x⁻¹) v = v
      rw [MulAut.mul_apply, MulAut.mul_apply, mem_fixV.mp hxv y hy]
      exact MulAut.apply_inv_self _ x v
  exact fun z hz => MulAction.mem_stabilizer_iff.mp (h hz)

private theorem rec418_core [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {k : ℕ} (hk : Odd k)
    (hk5 : 5 ≤ k) {L K : Subgroup (MulAut V)} (θ : L ≃* alternatingGroup (Fin (k + 2)))
    {b : Fin (k + 2)} (θ₀ : K ≃* alternatingGroup (Fin k))
    (hnat : IsNatSectionWith (altAct k) θ₀ (commV K) ⊥)
    (hC : ∀ w : V, (∀ x : L, (x : MulAut V) w = w) → w = 1) (hVL : commV L = ⊤)
    (θK : K ≃* alternatingGroup (Fin k)) (x y' g : MulAut V) (N : Subgroup (MulAut V))
    (c : Fin k) (hy' : y' ∈ K) (hx3 : x ^ 3 = 1) (hNK : N ≤ K)
    (hN : (N.subgroupOf K).map θK.toMonoidHom = altStabilizer k {c})
    (hxN : ∀ y ∈ N, x * y = y * x)
    (h3 : ((θK ⟨y', hy'⟩ : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)).IsThreeCycle)
    (hxg : x = g * y' * g⁻¹) (hgen : K ⊔ Subgroup.zpowers x = L)
    (hJ : ∀ z : L, θ z ∈ altStabilizer (k + 2) {b} →
      (z : MulAut V) ∈ K ⊔ K.map (MulAut.conj x).toMonoidHom)
    (hNFc : Nat.card ↥(commV (Subgroup.zpowers x)) = 4 →
      ∀ y ∈ N, ∀ f ∈ commV (Subgroup.zpowers x), y f = f) :
    IsNatSectionWith (altAct (k + 2)) θ (commV L) ⊥ := by
  have hk6 : k ≠ 6 := by
    rintro rfl
    exact absurd hk (by decide)
  have hnatK : IsNatSectionWith (altAct k) θK (commV K) ⊥ :=
    isNatSectionWith_of_equiv hk5 hk6 θ₀ θK hnat
  have hsplit := commV_sup_fixV_of_natural hk hk5 θK hnatK
  have hcard := card_commV_of_conj_threeCycle (by omega) θK hnatK hsplit hy' h3 hxg
  have hNF := hNFc hcard
  have hgen' : commV K ⊔ commV (Subgroup.zpowers x) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hVL, ← hgen]
    exact commV_sup_le _ _
  obtain ⟨v, hv1, hvK, hxvK⟩ :=
    exists_fixed_of_split_of_triv hV hk hk5 θK hnatK hNK c hN hx3 hxN hcard hNF hgen'
  have hEF := three_inf_commV_eq_bot_of_triv hV hk hk5 θK hnatK hNK c hN hx3 hxN hNF
  have hcardV : Nat.card V = 2 ^ (k + 2 - 1) := by
    rw [← nrr_card_mul (by rw [inf_comm]; exact hEF) hgen', hcard,
      card_commV_of_natural (by omega) θK hnatK, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  exact natural_of_fixed hV (by obtain ⟨m, rfl⟩ := hk; exact ⟨m + 1, by ring⟩) (by omega) θ hC b
    hv1 (fun z hz => nrr_fixed_sup hvK hxvK z (hJ z hz)) hcardV hVL

theorem rec418_gen [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {k : ℕ} (hk : Odd k) (hk5 : 5 ≤ k)
    {L K : Subgroup (MulAut V)} (θ : L ≃* alternatingGroup (Fin (k + 2))) {a b : Fin (k + 2)}
    (hab : a ≠ b) (hKL : K ≤ L)
    (hK : (K.subgroupOf L).map θ.toMonoidHom = altStabilizer (k + 2) {a, b})
    (θ₀ : K ≃* alternatingGroup (Fin k)) (hnat : IsNatSectionWith (altAct k) θ₀ (commV K) ⊥)
    (hC : ∀ w : V, (∀ x : L, (x : MulAut V) w = w) → w = 1) (hVL : commV L = ⊤)
    (hNtriv : ∀ (x : MulAut V) (hx : x ∈ L) (c : Fin (k + 2)), c ≠ a → c ≠ b →
      ((θ ⟨x, hx⟩ : alternatingGroup (Fin (k + 2))) : Equiv.Perm (Fin (k + 2))).IsThreeCycle →
      ((θ ⟨x, hx⟩ : alternatingGroup (Fin (k + 2))) : Equiv.Perm (Fin (k + 2))) a = b →
      ((θ ⟨x, hx⟩ : alternatingGroup (Fin (k + 2))) : Equiv.Perm (Fin (k + 2))) b = c →
      ((θ ⟨x, hx⟩ : alternatingGroup (Fin (k + 2))) : Equiv.Perm (Fin (k + 2))) c = a →
      ∀ n ∈ K, x * n = n * x → ∀ u ∈ commV (Subgroup.zpowers x), n u = u) :
    IsNatSectionWith (altAct (k + 2)) θ (commV L) ⊥ := by
  obtain ⟨θK, x, y', g, N, c, hy', hxL, -, hx3, hNK, hN, hxN, h3, hxg, hgen, hJ, c0, hc0a, hc0b,
    hxL', hx3c, hxa, hxb, hxc⟩ := exists_threeCycle_setup hk5 θ hab hKL hK
  exact rec418_core hV hk hk5 θ θ₀ hnat hC hVL θK x y' g N c hy' hx3 hNK hN hxN h3 hxg hgen hJ
    fun _ y hy f hf => hNtriv x hxL' c0 hc0a hc0b hx3c hxa hxb hxc y (hNK hy) (hxN y hy) f hf

theorem rec418 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {k : ℕ} (hk : Odd k) (hk7 : 7 ≤ k)
    {L K : Subgroup (MulAut V)} (θ : L ≃* alternatingGroup (Fin (k + 2))) {a b : Fin (k + 2)}
    (hab : a ≠ b) (hKL : K ≤ L)
    (hK : (K.subgroupOf L).map θ.toMonoidHom = altStabilizer (k + 2) {a, b})
    (θ₀ : K ≃* alternatingGroup (Fin k)) (hnat : IsNatSectionWith (altAct k) θ₀ (commV K) ⊥)
    (hC : ∀ w : V, (∀ x : L, (x : MulAut V) w = w) → w = 1) (hVL : commV L = ⊤) :
    IsNatSectionWith (altAct (k + 2)) θ (commV L) ⊥ := by
  obtain ⟨θK, x, y', g, N, c, hy', -, -, hx3, hNK, hN, hxN, h3, hxg, hgen, hJ, -⟩ :=
    exists_threeCycle_setup (by omega) θ hab hKL hK
  exact rec418_core hV hk (by omega) θ θ₀ hnat hC hVL θK x y' g N c hy' hx3 hNK hN hxN h3 hxg hgen
    hJ fun hcard => fix_commV_zpowers_of_stab (by omega) θK hNK c hN hxN hcard

end CFSG.CGT.PushingUpLit.CGT6
