module

public import CFSG.GH74.GLS.IVK.Statements.Sec9b
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.IVK

section Transport

variable {H H' : Type} [Group H] [Group H']

def comapEquiv (e : H ≃* H') (K : Subgroup H') : ↥(K.comap e.toMonoidHom) ≃* ↥K where
  toFun x := ⟨e x, x.2⟩
  invFun y := ⟨e.symm y, by simp [Subgroup.mem_comap]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := Subtype.ext (map_mul e (x : H) (y : H))

@[expose] def comapSylow {p : ℕ} (e : H ≃* H') (S : Sylow p H') : Sylow p H :=
  S.comapOfInjective e.toMonoidHom e.injective (fun x _ => ⟨e.symm x, by simp⟩)

theorem coe_comapSylow {p : ℕ} (e : H ≃* H') (S : Sylow p H') :
    (comapSylow e S : Subgroup H) = (S : Subgroup H').comap e.toMonoidHom :=
  rfl

theorem centralizer_comap (e : H ≃* H') (z : H) :
    (centralizer ({e z} : Set H')).comap e.toMonoidHom = centralizer ({z} : Set H) := by
  ext x
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

theorem oPrimeResidualOf_eq_closure {G : Type} [Group G] (p : ℕ) (X : Subgroup G) :
    oPrimeResidualOf p X = Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, x ^ p ^ k = 1} := by
  unfold oPrimeResidualOf oPrimeResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨y.2, k, by simpa using congrArg Subtype.val hk⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩

theorem oPrimeResidualOf_comap (e : H ≃* H') (p : ℕ) (K : Subgroup H') :
    oPrimeResidualOf p (K.comap e.toMonoidHom) = (oPrimeResidualOf p K).comap e.toMonoidHom := by
  rw [oPrimeResidualOf_eq_closure, oPrimeResidualOf_eq_closure,
    Subgroup.comap_equiv_eq_map_symm' e (Subgroup.closure _), MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, k, hk⟩
    exact ⟨e x, ⟨hx, k, by rw [← map_pow, hk, map_one]⟩, by simp⟩
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    exact ⟨by simpa using hy, k, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hk, map_one]⟩

theorem nonempty_mulEquiv_oPrimeResidual_centralizer (e : H ≃* H') (z : H) :
    Nonempty (↥(oPrimeResidualOf 2 (centralizer ({z} : Set H))) ≃*
      ↥(oPrimeResidualOf 2 (centralizer ({e z} : Set H')))) := by
  have h : oPrimeResidualOf 2 (centralizer ({z} : Set H)) =
      (oPrimeResidualOf 2 (centralizer ({e z} : Set H'))).comap e.toMonoidHom := by
    rw [← centralizer_comap e z, oPrimeResidualOf_comap]
  exact ⟨(MulEquiv.subgroupCongr h).trans (comapEquiv e _)⟩

theorem isInvolutionCentralizerOfModel_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    {t : StatedLieTag} {p' f' : ℕ} (h : IsInvolutionCentralizerOfModel Y t p' f') :
    IsInvolutionCentralizerOfModel X t p' f' := by
  obtain ⟨M, _, z', hM, ho, ⟨ψ⟩⟩ := h
  exact ⟨M, inferInstance, z', hM, ho, ⟨φ.trans ψ⟩⟩

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (h : IsElementaryAbelian p B) : IsElementaryAbelian p A :=
  CFSG.IsElementaryAbelian.of_mulEquiv φ.symm h

theorem mem_map_subtype_center {G : Type} [Group G] (T : Subgroup G) (x : G) :
    x ∈ (center ↥T).map T.subtype ↔ x ∈ T ∧ ∀ s ∈ T, s * x = x * s := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyc, rfl⟩
    refine ⟨hy, fun s hs => ?_⟩
    have := Subgroup.mem_center_iff.mp hyc ⟨s, hs⟩
    simpa using congrArg Subtype.val this
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2), rfl⟩

theorem zpowers_eq_center_comap (e : H ≃* H') (S : Subgroup H') (z : H)
    (h : zpowers (e z) = (center ↥S).map S.subtype) :
    zpowers z = (center ↥(S.comap e.toMonoidHom)).map (S.comap e.toMonoidHom).subtype := by
  ext x
  rw [mem_map_subtype_center]
  have hx : x ∈ zpowers z ↔ e x ∈ zpowers (e z) := by
    have h1 : (zpowers z).map e.toMonoidHom = zpowers (e z) :=
      MonoidHom.map_zpowers e.toMonoidHom z
    rw [← h1]
    exact (Subgroup.mem_map_iff_mem e.injective).symm
  rw [hx, h, mem_map_subtype_center]
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨hxS, hc⟩
    exact ⟨hxS, fun s hs => e.injective (by simpa only [map_mul] using hc (e s) hs)⟩
  · rintro ⟨hxS, hc⟩
    refine ⟨hxS, fun s hs => ?_⟩
    have := congrArg e (hc (e.symm s) (by simpa using hs))
    simpa using this

end Transport

theorem hyp94Loc_of_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {Gs : Type}
    [Group Gs] {z : H} {t : StatedLieTag} {p' f' : ℕ} (h : Hyp94Loc H' Gs (e z) t p' f') :
    Hyp94Loc H Gs z t p' f' := by
  obtain ⟨ht, hp', hp'2, p, f, S₀, U₀, hp, hp2, hGs, ⟨S', ⟨φ⟩⟩, hZ, hzU, hUS, hFour, hCent,
    hConj⟩ := h
  refine ⟨ht, hp', hp'2, p, f, comapSylow e S₀, U₀.comap e.toMonoidHom, hp, hp2, hGs,
    ⟨S', ⟨(comapEquiv e _).trans φ⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [coe_comapSylow]
    exact zpowers_eq_center_comap e _ z hZ
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_comap.mpr (Subgroup.zpowers_le.mp hzU))
  · rw [coe_comapSylow]
    exact Subgroup.comap_mono hUS
  · exact ⟨isElementaryAbelian_of_mulEquiv (comapEquiv e U₀) hFour.1,
      (Nat.card_congr (comapEquiv e U₀).toEquiv).trans hFour.2⟩
  · exact isInvolutionCentralizerOfModel_of_mulEquiv
      (nonempty_mulEquiv_oPrimeResidual_centralizer e z).some hCent
  · intro u hu v hv hu2 hv2
    have h := hConj (e u) hu (e v) hv (by rw [MulEquiv.orderOf_eq, hu2])
      (by rw [MulEquiv.orderOf_eq, hv2])
    simpa using (e.symm.toMonoidHom).map_isConj h

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
