module

public import CFSG.GH74.Uniqueness.SU.SU7Bar
public import CFSG.GH74.Uniqueness.SU.SU7Model

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5

namespace L191

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}

omit [Finite G] in
theorem exists_noncomm (hJ : J2Facts (S : Subgroup G) (Tsub S U) x z) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsT : s ∉ Tsub S U) (hs2 : s ^ 2 = 1) :
    ∃ c ∈ (S : Subgroup G), ∃ q₁ ∈ (S : Subgroup G) ⊓ centralizer ({x} : Set G),
      ∃ q₂ ∈ (S : Subgroup G) ⊓ centralizer ({x} : Set G), c * x * c⁻¹ = s ∧ q₁ * q₂ ≠ q₂ * q₁ := by
  obtain ⟨c, hcS, hcx⟩ := hJ.conj_invol s hsS hsT hs2
  obtain ⟨⟨e⟩, -, -, -, -, -⟩ := hJ.Q
  set Q : Subgroup G := Tsub S U ⊓ centralizer ({x} : Set G) with hQ
  have hQS : Q ≤ (S : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    inf_le_inf_right _ Base.T_le_S
  have hne : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
  refine ⟨c, hcS, (e.symm (QuaternionGroup.a 1) : G), hQS (e.symm (QuaternionGroup.a 1)).2,
    (e.symm (QuaternionGroup.xa 0) : G), hQS (e.symm (QuaternionGroup.xa 0)).2, hcx, ?_⟩
  intro h
  apply hne
  have h' : e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) =
      e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) := Subtype.ext h
  have h2 : e.symm (QuaternionGroup.a 1 * QuaternionGroup.xa 0) =
      e.symm (QuaternionGroup.xa 0 * QuaternionGroup.a 1) := by
    rw [map_mul, map_mul]; exact h'
  exact e.symm.injective h2

omit [Finite G] in
theorem card_cent {S T : Subgroup G} (hJ : J2Facts S T x z) {s : G} (hsS : s ∈ S) (hsT : s ∉ T)
    (hs2 : s ^ 2 = 1) : Nat.card ↥(S ⊓ centralizer ({s} : Set G)) = 16 := by
  obtain ⟨c, hcS, hcx⟩ := hJ.conj_invol s hsS hsT hs2
  obtain ⟨-, -, -, -, -, hcard⟩ := hJ.Q
  rw [← hcx, Gen.inf_centralizer_conj hcS x, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact hcard

omit [Finite G] in
theorem z_conj_mem {S T : Subgroup G} (hemb : J2Emb S T x) (hJ : J2Facts S T x z) {s g : G}
    (hsS : s ∈ S) (hsT : s ∉ T) (hs2 : s ^ 2 = 1)
    (hgc : ∀ c ∈ S ⊓ centralizer ({s} : Set G),
      g⁻¹ * c * g ∈ S ⊓ centralizer ({g⁻¹ * s * g} : Set G)) : g⁻¹ * z * g ∈ Zc T := by
  set C : Subgroup G := S ⊓ centralizer ({s} : Set G) with hC
  have hC16 : Nat.card C = 16 := card_cent hJ hsS hsT hs2
  set D : Subgroup G := C.map (MulAut.conj g⁻¹).toMonoidHom with hD
  have hDcard : Nat.card D = 16 := by
    rw [hD, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hC16]
  have hDS : D ≤ S := by
    rintro _ ⟨c, hc, rfl⟩
    have := (hgc c hc).1
    simpa [MulAut.conj_apply] using this
  have hTS : T ≤ S := hJ.T_le
  have hrel : T.relIndex S = 2 := by
    have h := Subgroup.relIndex_mul_card T S
    rw [inf_eq_left.2 hTS, hJ.card_T, hJ.card_S] at h
    omega
  have hle : T.relIndex D ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right (H := T) hDS (by rw [hrel]; norm_num)
    omega
  have hmul := Subgroup.relIndex_mul_card T D
  rw [hDcard] at hmul
  have hTD : 8 ≤ Nat.card ↥(T ⊓ D) := by
    have h3 : T.relIndex D = 0 ∨ T.relIndex D = 1 ∨ T.relIndex D = 2 := by omega
    rcases h3 with h | h | h <;> rw [h] at hmul <;> omega
  set M₀ : Subgroup G := (T ⊓ D).map (MulAut.conj g).toMonoidHom with hM₀
  have hM₀card : Nat.card M₀ = Nat.card ↥(T ⊓ D) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hM₀le : M₀ ≤ S ⊓ centralizer ({s} : Set G) := by
    rintro _ ⟨y, ⟨hyT, hyD⟩, rfl⟩
    obtain ⟨c, hcC, rfl⟩ := hyD
    have e : (MulAut.conj g).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom c) = c := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hcC
  obtain ⟨m, hm, hm2⟩ := hJ.sq_z s hsS hsT hs2 M₀ hM₀le (by omega)
  obtain ⟨y, ⟨hyT, -⟩, rfl⟩ := hm
  have hyz : g⁻¹ * z * g = y * y := by
    rw [← hm2]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pow_two]
    group
  rw [hyz]
  exact Model.sq_mem_Zc hemb y hyT

end L191

open CFSG.GH74.Uniqueness.SU.SU7.L191 in
theorem lemma191 : Lemma191Stmt := by
  intro G _ _ S U M V x z A B R hc s hsS hsT hs2 u huU hu1 huz
  have hH := hc.hyp
  have hconf := hc.conf
  have hcl := hc.concl
  have hJ := Base.j2facts hH hconf hcl
  have hemb := (Base.emb_zgen hH hconf hcl).1
  have hmemZ := Base.mem_Zc_iff hH hconf hcl
  have hxS := Base.x_mem_S hconf
  have hx2 := Base.x_mul_self hconf
  have hs2' : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
  have hss : s * s = 1 := by rw [← pow_two]; exact hs2'
  have hcov : ∀ s' ∈ (S : Subgroup G), s' ∈ Tsub S U ∨ s⁻¹ * s' ∈ Tsub S U := by
    intro s' hs'
    rcases hJ.S_cover s' hs' with h | h
    · exact Or.inl h
    · rcases hJ.S_cover s hsS with h' | h'
      · exact absurd h' hsT
      · right
        have e : s⁻¹ * s' = (x * s)⁻¹ * (x * s') := by group
        rw [e]
        exact (Tsub S U).mul_mem ((Tsub S U).inv_mem h') h
  obtain ⟨g, hgT, hgc⟩ := Gen.thompson_two hH.simple hH.nonab S.isPGroup'
    (Sylow.not_dvd_index S) hJ.T_normal hsS hsT hss hcov
  have hs'2 : (g⁻¹ * s * g) * (g⁻¹ * s * g) = 1 := by
    calc g⁻¹ * s * g * (g⁻¹ * s * g) = g⁻¹ * (s * s) * g := by group
      _ = 1 := by rw [hss]; group
  have hs'1 : g⁻¹ * s * g ≠ 1 := by
    intro h
    have : s = 1 := by
      have h2 : g * (g⁻¹ * s * g) * g⁻¹ = g * 1 * g⁻¹ := by rw [h]
      simpa [mul_assoc] using h2
    rw [this] at hsT
    exact hsT (Tsub S U).one_mem
  have hs'U : g⁻¹ * s * g ∈ U := by
    by_contra hnot
    obtain ⟨A', B', hL, -, -, -, hcA, hcB⟩ := hJ.AB
    obtain ⟨c, hcS, q₁, hq₁, q₂, hq₂, hcx, hq12⟩ := exists_noncomm hJ hsS hsT hs2'
    have hs'T := hgT
    have hs'2' : (g⁻¹ * s * g) ^ 2 = 1 := by rw [pow_two]; exact hs'2
    have hkey : ∀ E : Subgroup G, Open.IsElemAbelian 2 E →
        (∀ g' ∈ (S : Subgroup G), g' * (g⁻¹ * s * g) = (g⁻¹ * s * g) * g' → g' ∈ E) → False := by
      intro E hE hcE
      have hEc := (isElemAbelian_iff.1 hE).1
      have hconjmem : ∀ q ∈ (S : Subgroup G) ⊓ centralizer ({x} : Set G),
          g⁻¹ * (c * q * c⁻¹) * g ∈ E := by
        intro q hq
        have hcq : c * q * c⁻¹ ∈ (S : Subgroup G) ⊓ centralizer ({s} : Set G) := by
          refine Subgroup.mem_inf.2 ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hcS
            (Subgroup.mem_inf.1 hq).1) ((S : Subgroup G).inv_mem hcS), ?_⟩
          rw [mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          have hqx : x * q = q * x := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hq).2 x
            (Set.mem_singleton x)
          rw [← hcx]
          calc c * x * c⁻¹ * (c * q * c⁻¹) = c * (x * q) * c⁻¹ := by group
            _ = c * (q * x) * c⁻¹ := by rw [hqx]
            _ = c * q * c⁻¹ * (c * x * c⁻¹) := by group
        have h1 := hgc _ hcq
        have h2 := Subgroup.mem_inf.1 h1
        apply hcE _ h2.1
        have := mem_centralizer_iff.1 h2.2 (g⁻¹ * s * g) (Set.mem_singleton _)
        exact this.symm
      have h1 := hconjmem q₁ hq₁
      have h2 := hconjmem q₂ hq₂
      have h3 := hEc _ h1 _ h2
      apply hq12
      have e : (g⁻¹ * (c * q₁ * c⁻¹) * g) * (g⁻¹ * (c * q₂ * c⁻¹) * g) =
          g⁻¹ * (c * (q₁ * q₂) * c⁻¹) * g := by group
      have e' : (g⁻¹ * (c * q₂ * c⁻¹) * g) * (g⁻¹ * (c * q₁ * c⁻¹) * g) =
          g⁻¹ * (c * (q₂ * q₁) * c⁻¹) * g := by group
      rw [e, e'] at h3
      have h4 : c * (q₁ * q₂) * c⁻¹ = c * (q₂ * q₁) * c⁻¹ := by
        exact mul_left_cancel (mul_right_cancel h3)
      exact mul_left_cancel (mul_right_cancel h4)
    rcases hL.invol _ hs'T hs'1 hs'2' with hA | hB
    · have hnB : g⁻¹ * s * g ∉ B' := fun hB => hnot (by
        have : g⁻¹ * s * g ∈ A' ⊓ B' := ⟨hA, hB⟩
        rw [hL.inf_eq] at this
        exact (hmemZ _).1 this)
      exact hkey A' hL.A_E.1 (fun g' hg' hcomm => (hcA _ hA hnB g' hg').1 hcomm)
    · have hnA : g⁻¹ * s * g ∉ A' := fun hA => hnot (by
        have : g⁻¹ * s * g ∈ A' ⊓ B' := ⟨hA, hB⟩
        rw [hL.inf_eq] at this
        exact (hmemZ _).1 this)
      exact hkey B' hL.B_E.1 (fun g' hg' hcomm => (hcB _ hB hnA g' hg').1 hcomm)
  have hzg : g⁻¹ * z * g ∈ U := (hmemZ _).1 (z_conj_mem hemb hJ hsS hsT hs2' hgc)
  have hzU : z ∈ U := (hmemZ z).1 hJ.z_mem
  have hz1 := Base.z_ne_one hconf
  have hzg1 : g⁻¹ * z * g ≠ 1 := by
    intro h
    apply hz1
    have h2 : g * (g⁻¹ * z * g) * g⁻¹ = g * 1 * g⁻¹ := by rw [h]
    simpa [mul_assoc] using h2
  have hne : g⁻¹ * s * g ≠ g⁻¹ * z * g := by
    intro h
    apply hsT
    have hsz : s = z := mul_left_cancel (mul_right_cancel h)
    rw [hsz]
    exact (mem_Zc.1 hJ.z_mem).1
  obtain ⟨a, haM, haT, hafix⟩ := Bar.exists_fpf hH hconf hcl
  have hUsub : ∀ n ∈ normalizer (U : Set G), ∀ p ∈ U, n * p * n⁻¹ ∈ U :=
    fun n hn p hp => (mem_normalizer_iff.1 hn p).1 hp
  have haU : a ∈ normalizer (U : Set G) := by
    have hconj : ∀ p ∈ U, a * p * a⁻¹ ∈ U := fun p hp =>
      (hmemZ _).1 (Base.mem_Zc_of_normalizer haT ((hmemZ p).2 hp))
    exact Gen.mem_normalizer_of_conj_le hconj
  have hxU : x ∈ normalizer (U : Set G) := hH.normal hxS
  have hU4 : Nat.card U = 4 := by rw [hH.four.2.2]; norm_num
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := (isElemAbelian_iff.1 hH.four.2.1).1
  have hU2 : ∀ a ∈ U, a * a = 1 := fun a ha => by
    rw [← pow_two]; exact (isElemAbelian_iff.1 hH.four.2.1).2 a ha
  have hxz : x * z * x⁻¹ = z := by
    rw [hconf.z_center x hxS]; group
  have hxfix : ∀ p ∈ U, p ≠ 1 → p ≠ z → x * p * x⁻¹ ≠ p := by
    intro p hp hp1 hpz heq
    have h1 : x * p = p * x := by
      have := heq
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    exact hJ.x_not_mem ((hJ.half_central p ((hmemZ p).2 hp) hp1 hpz x hxS).1 h1)
  obtain ⟨h, hhN, h1, h2⟩ := Gen.two_trans hU4 hUc hU2 hUsub haU hxU hzU hz1 hxz hafix hxfix
    (g⁻¹ * s * g) hs'U (g⁻¹ * z * g) hzg u huU z hzU hs'1 hzg1 hne hu1 hz1 huz
  refine ⟨g * h⁻¹, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hcz : (g * h⁻¹)⁻¹ * z * (g * h⁻¹) = z := by
      have : (g * h⁻¹)⁻¹ * z * (g * h⁻¹) = h * (g⁻¹ * z * g) * h⁻¹ := by group
      rw [this]; exact h2
    calc z * (g * h⁻¹) = (g * h⁻¹) * ((g * h⁻¹)⁻¹ * z * (g * h⁻¹)) := by group
      _ = (g * h⁻¹) * z := by rw [hcz]
  · have : (g * h⁻¹)⁻¹ * s * (g * h⁻¹) = h * (g⁻¹ * s * g) * h⁻¹ := by group
    rw [this]; exact h1

end CFSG.GH74.Uniqueness.SU.SU7
