module

public import CFSG.ClassicalInvolution.Q3.TL3CentStep
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3Z

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem isPGroup_center (hc : TightCls Y R S t) : IsPGroup 2 ↥(Subgroup.center Y) := by
  have hZnil : Group.IsNilpotent ↥(Subgroup.center Y) := by
    refine Subgroup.isNilpotent_of_ker_le_center (1 : ↥(Subgroup.center Y) →* Unit) ?_
    intro z _
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_center_iff.mp z.2 w)
  exact (isPGroup_two_genFittingFitting hc.2.2).to_le
    (le_sSup ⟨inferInstance, hZnil⟩ : Subgroup.center Y ≤ genFittingFitting Y)

theorem not_mem_center (hc : TightCls Y R S t) (hE2 : ¬ TightInO2 t) :
    t ∉ Subgroup.center Y :=
  fun h => hE2 ⟨_, inferInstance, isPGroup_center hc, h⟩

theorem noTwin (hd : TightDatum R S t) (hE : TightEdgeless R) :
    ∀ y : Y, ∀ c ∈ Subgroup.center Y, y * t * y⁻¹ = t * c → c = 1 := by
  intro y c hc hy
  by_contra hc1
  exact hd.not_edgeless_of_twin hc hc1 hy hE

theorem center_quot_eq_bot (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hE2 : ¬ TightInO2 t) : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
  set Z := Subgroup.center Y
  rw [eq_bot_iff]
  intro xb hxb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z xb
  set C := Subgroup.zpowers (QuotientGroup.mk' Z x)
  have hCn : C.Normal := ⟨fun c hc g => by
    rw [Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hxb hc) g, mul_inv_cancel_right]
    exact hc⟩
  set H : Subgroup Y := C.comap (QuotientGroup.mk' Z)
  have hHn : H.Normal := hCn.comap _
  let f : ↥H →* ↥C := ((QuotientGroup.mk' Z).comp H.subtype).codRestrict C fun h => h.2
  have hf : f.ker ≤ Subgroup.center ↥H := by
    intro h hh
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 : (h : Y) ∈ Z :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hh))
    exact Subtype.ext (Subgroup.mem_center_iff.mp h1 w)
  have hHc := f.isMulCommutative_of_isCyclic_of_ker_le_center hf
  have hHnil : Group.IsNilpotent ↥H := by
    refine Subgroup.isNilpotent_of_ker_le_center (1 : ↥H →* Unit) ?_
    intro z _
    rw [Subgroup.mem_center_iff]
    intro w
    exact hHc.is_comm.comm w z
  have hxH : x ∈ H := Subgroup.mem_zpowers _
  have hxZ : x ∈ Z := hd.genFittingFitting_le_center hc hE2
    ((le_sSup ⟨hHn, hHnil⟩ : H ≤ genFittingFitting Y) hxH)
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr hxZ

theorem acts3_of_map {N : Subgroup Y} [N.Normal] (hd : TightDatum R S t)
    (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N)
    (hnt : ∀ y : Y, ∀ n ∈ N, y * t * y⁻¹ = t * n → n = 1)
    (h : TightActs3 (R.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N t)) :
    TightActs3 R t := by
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  obtain ⟨xb, k, hxbC, hxb3, rb, hrb, hxr⟩ := h
  rw [TwistQ.centralizer_mk_eq hnt] at hxbC
  obtain ⟨x, hxC, rfl⟩ := hxbC
  have hxN : x ^ 3 ^ k ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    rw [← map_pow] at hxb3
    exact hxb3
  obtain ⟨n, hnN, hn⟩ : ∃ n ∈ N, n ^ 3 ^ k = (x ^ 3 ^ k)⁻¹ := by
    have hcop : (Nat.card ↥N).Coprime (3 ^ k) := by
      obtain ⟨a, ha⟩ := hN2.exists_card_eq
      rw [ha]
      exact Nat.Coprime.pow _ _ (by norm_num)
    obtain ⟨m, hm⟩ := (powCoprime hcop).surjective ⟨(x ^ 3 ^ k)⁻¹, N.inv_mem hxN⟩
    exact ⟨m, m.2, congrArg Subtype.val hm⟩
  have hnZ : ∀ a : Y, a * n = n * a := Subgroup.mem_center_iff.mp (hNc hnN)
  have hnC : n ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hnZ t).symm
  have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hnN
  refine ⟨x * n, k, Subgroup.mul_mem _ hxC hnC, ?_, ?_⟩
  · rw [(show Commute x n from hnZ x).mul_pow, hn, mul_inv_cancel]
  · obtain ⟨r, hr, rfl⟩ := hrb
    refine ⟨r, hr, fun hmem => hxr ?_⟩
    have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hmem
    rwa [TwistQ.oddCoreImg_map hRN, map_commutatorElement, map_mul, hn1, mul_one] at h1

omit [Finite Y] in
theorem eq_one_of_quot (hc : TightCls Y R S t) {γ : MulAut Y}
    (hγZ : ∀ x, QuotientGroup.mk' (Subgroup.center Y) (γ x) =
      QuotientGroup.mk' (Subgroup.center Y) x)
    (hγK : ∀ x ∈ tightCore R, γ x = x) : γ = 1 := by
  have hle : (⨆ g : Y, conjSub g (tightCore R)) ≤
      γ.toMonoidHom.eqLocus (MonoidHom.id Y) := by
    refine iSup_le fun g => ?_
    rintro _ ⟨k, hk, rfl⟩
    set m := g⁻¹ * γ g with hm
    have hmZ : m ∈ Subgroup.center Y := by
      rw [hm, ← QuotientGroup.eq]
      exact (hγZ g).symm
    have hg : γ g = g * m := by rw [hm, mul_inv_cancel_left]
    have hmc : ∀ a : Y, a * m = m * a := Subgroup.mem_center_iff.mp hmZ
    show γ (g * k * g⁻¹) = g * k * g⁻¹
    rw [map_mul, map_mul, map_inv, hγK k hk, hg]
    calc g * m * k * (g * m)⁻¹ = g * (m * k) * m⁻¹ * g⁻¹ := by group
      _ = g * (k * m) * m⁻¹ * g⁻¹ := by rw [← hmc k]
      _ = g * k * g⁻¹ := by group
  have htop : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hc.2.1
  ext x
  exact hle (by rw [htop]; exact Subgroup.mem_top x)

theorem concl163_of_quot (hd : TightDatum R S t) (hc : TightCls Y R S t) (hE2 : ¬ TightInO2 t)
    (h : Concl163 (R.map (QuotientGroup.mk' (Subgroup.center Y)))
      (QuotientGroup.mk' (Subgroup.center Y) t)) : Concl163 R t := by
  set Z := Subgroup.center Y with hZdef
  have hRN : R ⊓ Z = ⊥ := TwistQ.inf_eq_bot hd (isPGroup_center hc) (not_mem_center hc hE2)
  intro β hβ2 hβK
  have hβZ : (Subgroup.center Y).map (β : Y →* Y) = Subgroup.center Y := Subgroup.map_center_eq β
  let βb : MulAut (Y ⧸ Z) := QuotientGroup.congr Z Z β hβZ
  have hβb : ∀ x : Y, βb (QuotientGroup.mk' Z x) = QuotientGroup.mk' Z (β x) :=
    fun x => QuotientGroup.congr_mk' Z Z β hβZ x
  have hβb2 : βb * βb = 1 := by
    ext xb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z xb
    rw [MulAut.mul_apply, hβb, hβb, ← MulAut.mul_apply, hβ2, MulAut.one_apply, MulAut.one_apply]
  have hβbK : ∀ xb ∈ tightCore (R.map (QuotientGroup.mk' Z)), βb xb = xb := by
    rw [← TwistQ.tightCore_map hRN]
    rintro _ ⟨k, hk, rfl⟩
    rw [hβb, hβK k hk]
  rcases h βb hβb2 hβbK with h1 | h1
  · left
    refine eq_one_of_quot hc (fun x => ?_) hβK
    have h2 := DFunLike.congr_fun h1 (QuotientGroup.mk' Z x)
    rwa [hβb, MulAut.one_apply] at h2
  · right
    have hγ : (MulAut.conj t)⁻¹ * β = 1 := by
      refine eq_one_of_quot hc (fun x => ?_) (fun x hx => ?_)
      · have h2 := DFunLike.congr_fun h1 (QuotientGroup.mk' Z x)
        rw [hβb, MulAut.conj_apply] at h2
        rw [MulAut.mul_apply, ← map_inv, MulAut.conj_apply, map_mul, map_mul, h2]
        simp only [map_inv]
        group
        rfl
      · have hxt : x * t = t * x :=
          Subgroup.mem_centralizer_singleton_iff.mp (hd.cent (tightCore_le R hx))
        rw [MulAut.mul_apply, hβK x hx, ← map_inv, MulAut.conj_apply]
        calc t⁻¹ * x * t⁻¹⁻¹ = t⁻¹ * (x * t) := by group
          _ = t⁻¹ * (t * x) := by rw [hxt]
          _ = x := by group
    calc β = MulAut.conj t * ((MulAut.conj t)⁻¹ * β) := by rw [mul_inv_cancel_left]
      _ = MulAut.conj t := by rw [hγ, mul_one]

end CFSG.ClassicalInvolution.Q3.TL4.E3S3Z
