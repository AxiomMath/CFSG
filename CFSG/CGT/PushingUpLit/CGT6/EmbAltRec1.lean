module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltModFix
import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltMod

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUp

variable {V : Type} [CommGroup V] {k : ℕ}

private def nr1Comm (x : MulAut V) : V →* V :=
  MonoidHom.mk' (fun v => x v * v⁻¹) fun a b => by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

private theorem nr1Comm_apply (x : MulAut V) (v : V) : nr1Comm x v = x v * v⁻¹ := rfl

private theorem nr1_commV_zpowers (x : MulAut V) :
    commV (Subgroup.zpowers x) = (nr1Comm x).range := by
  have key : ∀ y ∈ Subgroup.zpowers x, ∀ v : V, y v * v⁻¹ ∈ (nr1Comm x).range := by
    intro y hy
    rw [Subgroup.zpowers_eq_closure] at hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      intro v
      rw [Set.mem_singleton_iff.mp hy]
      exact ⟨v, rfl⟩
    | one => intro v; simp
    | mul a b _ _ ha hb =>
      intro v
      have : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
        simp [MulAut.mul_apply]
      rw [this]
      exact mul_mem (ha (b v)) (hb v)
    | inv a _ ha =>
      intro v
      have : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
        simp
      rw [this]
      exact inv_mem (ha (a⁻¹ v))
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ?_
  · rintro w ⟨y, hy, v, rfl⟩
    exact key y hy v
  · rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, v, rfl⟩

private theorem nr1_eq_one_of_fix (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V} (hx3 : x ^ 3 = 1)
    {f : V} (hf : f ∈ commV (Subgroup.zpowers x)) (hfx : x f = f) : f = 1 := by
  rw [nr1_commV_zpowers] at hf
  obtain ⟨v, rfl⟩ := hf
  have hinv : ∀ u : V, u⁻¹ = u := fun u =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV u)
  have h3 : x (x (x v)) = v := by
    have := congrArg (fun g : MulAut V => g v) hx3
    simpa [pow_succ, MulAut.mul_apply] using this
  rw [nr1Comm_apply, map_mul, map_inv] at hfx
  simp only [hinv] at hfx
  have h1 : x (x v) = v := mul_right_cancel (hfx.trans (mul_comm _ _))
  have h2 : x v = v := (congrArg x h1).symm.trans h3
  rw [nr1Comm_apply, h2, mul_inv_cancel]

private def nr1Act (F : Subgroup V) (N : Subgroup (MulAut V))
    (hF : ∀ y ∈ N, ∀ f ∈ F, y f ∈ F) : N →* Equiv.Perm ↥F where
  toFun y := MulAut.toPerm ↥F
    (restrictAut (y : MulAut V) F (hF y y.2) (hF (y : MulAut V)⁻¹ (N.inv_mem y.2)))
  map_one' := by ext f; rfl
  map_mul' a b := by ext f; rfl

private theorem nr1_fix_of_simple {F : Subgroup V} (hF4 : Nat.card F = 4)
    {N : Subgroup (MulAut V)} (hF : ∀ y ∈ N, ∀ f ∈ F, y f ∈ F) [IsSimpleGroup N]
    (hbig : 24 < Nat.card N) : ∀ y ∈ N, ∀ f ∈ F, y f = f := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  rcases (nr1Act F N hF).normal_ker.eq_bot_or_eq_top with h0 | h1
  · exfalso
    have hinj : Function.Injective (nr1Act F N hF) := (MonoidHom.ker_eq_bot_iff _).mp h0
    have h := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm, hF4] at h
    have h24 : Nat.factorial 4 = 24 := rfl
    omega
  · intro y hy f hf
    have h2 : (⟨y, hy⟩ : N) ∈ (nr1Act F N hF).ker := by rw [h1]; trivial
    exact congrArg (fun p : Equiv.Perm F => (p ⟨f, hf⟩ : V)) (MonoidHom.mem_ker.mp h2)

private theorem nr1_stab {K : Subgroup (MulAut V)} (θ : K ≃* alternatingGroup (Fin k))
    {N : Subgroup (MulAut V)} (hNK : N ≤ K) (c : Fin k)
    (hN : (N.subgroupOf K).map θ.toMonoidHom = altStabilizer k {c}) (hk : 6 ≤ k) :
    IsSimpleGroup N ∧ 24 < Nat.card N := by
  have hm : 5 ≤ k - ({c} : Finset (Fin k)).card := by simp; omega
  let e : N ≃* alternatingGroup (Fin (k - ({c} : Finset (Fin k)).card)) :=
    (((Subgroup.subgroupOfEquivOfLe hNK).symm.trans
      (Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective)).trans
        (MulEquiv.subgroupCongr hN)).trans (altStabilizerEquiv {c})
  have : IsSimpleGroup (alternatingGroup (Fin (k - ({c} : Finset (Fin k)).card))) :=
    alternatingGroup.isSimpleGroup (by simpa using hm)
  refine ⟨e.isSimpleGroup, ?_⟩
  have : Nontrivial (Fin (k - ({c} : Finset (Fin k)).card)) :=
    Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  have h5 : Nat.factorial 5 ≤ Nat.factorial (k - ({c} : Finset (Fin k)).card) :=
    Nat.factorial_le hm
  have h120 : Nat.factorial 5 = 120 := rfl
  omega

private theorem nr1_card_sup {W : Type*} [CommGroup W] {A B : Subgroup W} (hAB : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  let ψ : A × B →* W := A.subtype.coprod B.subtype
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : (a : W) * b = 1 := hab
    have hab' : (a : W) = (b : W)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h2 : (a : W) ∈ A ⊓ B :=
      Subgroup.mem_inf.mpr ⟨a.2, by rw [hab']; exact inv_mem b.2⟩
    rw [hAB, Subgroup.mem_bot] at h2
    have h3 : (b : W) = 1 := by rw [h2, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  have hrange : ψ.range = A ⊔ B := by
    ext w
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact Subgroup.mul_mem_sup a.2 b.2
    · intro hw
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private theorem nr1_apply_comm {N : Subgroup (MulAut V)} {x : MulAut V}
    (hxN : ∀ y ∈ N, x * y = y * x) : ∀ y ∈ N, ∀ v : V, x (y v) = y (x v) := by
  intro y hy v
  have := congrArg (fun f : MulAut V => f v) (hxN y hy)
  simpa [MulAut.mul_apply] using this

private theorem nr1_comm_inv {N : Subgroup (MulAut V)} {x : MulAut V}
    (hcomm : ∀ y ∈ N, ∀ v : V, x (y v) = y (x v)) {w : V} (hw : w ∈ commV N) :
    x w ∈ commV N := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨y, hy, v, rfl⟩ := hw
    rw [map_mul, map_inv, hcomm y hy v]
    exact Subgroup.subset_closure ⟨y, hy, x v, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

private theorem nr1_inv {N : Subgroup (MulAut V)} {x : MulAut V}
    (hxN : ∀ y ∈ N, x * y = y * x) :
    ∀ y ∈ N, ∀ f ∈ commV (Subgroup.zpowers x), y f ∈ commV (Subgroup.zpowers x) := by
  have hcomm := nr1_apply_comm hxN
  intro y hy f hf
  rw [nr1_commV_zpowers] at hf ⊢
  obtain ⟨v, rfl⟩ := hf
  refine ⟨y v, ?_⟩
  rw [nr1Comm_apply, nr1Comm_apply, map_mul, map_inv, hcomm y hy v]

theorem fix_commV_zpowers_of_stab {K : Subgroup (MulAut V)} (hk : 6 ≤ k)
    (θ : K ≃* alternatingGroup (Fin k)) {N : Subgroup (MulAut V)} (hNK : N ≤ K) (c : Fin k)
    (hN : (N.subgroupOf K).map θ.toMonoidHom = altStabilizer k {c}) {x : MulAut V}
    (hxN : ∀ y ∈ N, x * y = y * x) (hcard : Nat.card ↥(commV (Subgroup.zpowers x)) = 4) :
    ∀ y ∈ N, ∀ f ∈ commV (Subgroup.zpowers x), y f = f := by
  obtain ⟨hsimple, hbig⟩ := nr1_stab θ hNK c hN hk
  have := hsimple
  exact nr1_fix_of_simple hcard (nr1_inv hxN) hbig

theorem three_inf_commV_eq_bot_of_triv (hV : ∀ v : V, v ^ 2 = 1) (hk : Odd k) (hk5 : 5 ≤ k)
    {K : Subgroup (MulAut V)} (θ : K ≃* alternatingGroup (Fin k))
    (h : IsNatSectionWith (altAct k) θ (commV K) ⊥) {N : Subgroup (MulAut V)} (hNK : N ≤ K)
    (c : Fin k) (hN : (N.subgroupOf K).map θ.toMonoidHom = altStabilizer k {c})
    {x : MulAut V} (hx3 : x ^ 3 = 1) (hxN : ∀ y ∈ N, x * y = y * x)
    (hNF : ∀ y ∈ N, ∀ f ∈ commV (Subgroup.zpowers x), y f = f) :
    commV (Subgroup.zpowers x) ⊓ commV K = ⊥ := by
  have hcomm := nr1_apply_comm hxN
  obtain ⟨w, hw1, hwN, hwfix, hw⟩ := exists_fixed_pair_of_natural hk hk5 θ h hNK c hN
  have hxw : x w = w := by
    have h1 : x w ∈ commV N := nr1_comm_inv hcomm hwN
    have h2 : x w ∈ fixV N := mem_fixV.mpr fun y hy => by
      rw [← hcomm y hy w, mem_fixV.mp hwfix y hy]
    rcases hw (x w) (commV_mono hNK h1) h2 with h3 | h3
    · exact absurd ((map_eq_one_iff x x.injective).mp h3) hw1
    · exact h3
  refine eq_bot_iff.mpr fun u hu => ?_
  obtain ⟨huF, huE⟩ := hu
  have huN : u ∈ fixV N := mem_fixV.mpr fun y hy => hNF y hy u huF
  rcases hw u huE huN with h3 | h3
  · exact Subgroup.mem_bot.mpr h3
  · rw [h3] at huF
    exact absurd (nr1_eq_one_of_fix hV hx3 huF hxw) hw1

theorem exists_fixed_of_split_of_triv [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hk : Odd k)
    (hk5 : 5 ≤ k) {K : Subgroup (MulAut V)} (θ : K ≃* alternatingGroup (Fin k))
    (h : IsNatSectionWith (altAct k) θ (commV K) ⊥) {N : Subgroup (MulAut V)} (hNK : N ≤ K)
    (c : Fin k) (hN : (N.subgroupOf K).map θ.toMonoidHom = altStabilizer k {c})
    {x : MulAut V} (hx3 : x ^ 3 = 1) (hxN : ∀ y ∈ N, x * y = y * x)
    (hcard : Nat.card ↥(commV (Subgroup.zpowers x)) = 4)
    (hNF : ∀ y ∈ N, ∀ f ∈ commV (Subgroup.zpowers x), y f = f)
    (hgen : commV K ⊔ commV (Subgroup.zpowers x) = ⊤) :
    ∃ v : V, v ≠ 1 ∧ v ∈ fixV K ∧ (x⁻¹ : MulAut V) v ∈ fixV K := by
  have hEF := three_inf_commV_eq_bot_of_triv hV hk hk5 θ h hNK c hN hx3 hxN hNF
  have hE : Nat.card (commV K) = 2 ^ (k - 1) := card_commV_of_natural (by omega) θ h
  have hEC := commV_inf_fixV_of_natural hk (by omega) θ h
  have hsplit := commV_sup_fixV_of_natural hk hk5 θ h
  have h1 : Nat.card V = Nat.card (commV K) * Nat.card (commV (Subgroup.zpowers x)) := by
    rw [← Subgroup.card_top (G := V), ← hgen]
    exact nr1_card_sup (by rw [inf_comm]; exact hEF)
  have h2 : Nat.card V = Nat.card (commV K) * Nat.card (fixV K) := by
    rw [← Subgroup.card_top (G := V), ← hsplit]
    exact nr1_card_sup hEC
  have hC : Nat.card (fixV K) = 4 := by
    have hpos : 0 < Nat.card (commV K) := by rw [hE]; positivity
    have h3 := h1.symm.trans h2
    rw [hcard] at h3
    exact (Nat.eq_of_mul_eq_mul_left hpos h3).symm
  have hCD : fixV K ≤ fixV N := fun v hv => mem_fixV.mpr fun y hy => mem_fixV.mp hv y (hNK hy)
  have hcomm := nr1_apply_comm hxN
  obtain ⟨w, hw1, hwN, hwfix, hw⟩ := exists_fixed_pair_of_natural hk hk5 θ h hNK c hN
  have hDE : fixV N ⊓ commV K ≤ Subgroup.zpowers w := by
    intro u hu
    rcases hw u hu.2 hu.1 with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
  have hDE2 : Nat.card ↥(fixV N ⊓ commV K) ≤ 2 :=
    calc Nat.card ↥(fixV N ⊓ commV K) ≤ Nat.card ↥(Subgroup.zpowers w) :=
          Subgroup.card_le_of_le hDE
      _ = orderOf w := Nat.card_zpowers w
      _ ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hV w))
  have hD8 : Nat.card ↥(fixV N) ≤ 8 := by
    let g : ↥(fixV N ⊓ commV K) × ↥(fixV K) → ↥(fixV N) := fun p =>
      ⟨(p.1 : V) * p.2, mul_mem (Subgroup.mem_inf.mp p.1.2).1 (hCD p.2.2)⟩
    have hg : Function.Surjective g := by
      intro d
      have hd : (d : V) ∈ commV K ⊔ fixV K := by rw [hsplit]; trivial
      obtain ⟨e, he, c', hc', hec⟩ := Subgroup.mem_sup.mp hd
      have heD : e ∈ fixV N := by
        have : e = (d : V) * c'⁻¹ := by rw [← hec, mul_inv_cancel_right]
        rw [this]
        exact mul_mem d.2 (inv_mem (hCD hc'))
      exact ⟨(⟨e, Subgroup.mem_inf.mpr ⟨heD, he⟩⟩, ⟨c', hc'⟩), Subtype.ext hec⟩
    have := Nat.card_le_card_of_surjective g hg
    rw [Nat.card_prod, hC] at this
    omega
  by_contra hcon
  have hinf : fixV K ⊓ (fixV K).map x.toMonoidHom = ⊥ := by
    refine eq_bot_iff.mpr fun v hv => ?_
    by_contra hv1
    obtain ⟨hvC, c', hc', rfl⟩ := hv
    exact hcon ⟨x c', hv1, hvC, by simpa using hc'⟩
  have hxCD : (fixV K).map x.toMonoidHom ≤ fixV N := by
    rintro _ ⟨c', hc', rfl⟩
    exact mem_fixV.mpr fun y hy => by
      show y (x c') = x c'
      rw [← hcomm y hy c', mem_fixV.mp hc' y (hNK hy)]
  have hxC : Nat.card ↥((fixV K).map x.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective x.injective, hC]
  have h16 := nr1_card_sup hinf
  rw [hC, hxC] at h16
  have h17 := Subgroup.card_le_of_le (sup_le hCD hxCD)
  omega

end CFSG.CGT.PushingUpLit.CGT6
