module

public import CFSG.CGT.PushingUpLit.A78G0.DualAux
public import CFSG.CGT.PushingUpLit.A78G0.DualData
public import CFSG.CGT.PushingUpLit.A78.BenderTI
public import CFSG.CGT.PushingUpLit.A78G0.TLemma
public import CFSG.CGT.PushingUpLit.A78G0.KFacts

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
  CFSG.CGT.PushingUpLit.A78S4 CFSG.ABGLocalTools Matrix

section Conj

variable {G : Type} [Group G]

theorem cs_conj_normalizes {Z : Subgroup G} {g η : G}
    (hη : η ∈ Subgroup.normalizer ((cs Z g : Subgroup G) : Set G)) :
    cs Z (g⁻¹ * η * g) = Z := by
  rw [mul_assoc, cs_mul, cs_mul, cs_of_mem_normalizer hη, cs_cs_inv]

theorem cs_conj_centralizes {Z : Subgroup G} {g η : G} (hηZ : ∀ z ∈ Z, η * z * η⁻¹ = z) {x : G}
    (hx : x ∈ cs Z g⁻¹) : (g⁻¹ * η * g) * x * (g⁻¹ * η * g)⁻¹ = x := by
  have hz : g * x * g⁻¹ ∈ Z := by
    have := mem_cs.1 hx
    simpa using this
  calc (g⁻¹ * η * g) * x * (g⁻¹ * η * g)⁻¹ = g⁻¹ * (η * (g * x * g⁻¹) * η⁻¹) * g := by group
    _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hηZ _ hz]
    _ = x := by group

theorem conj_pow_eq_one {g η : G} {n : ℕ} (hη : η ^ n = 1) : (g⁻¹ * η * g) ^ n = 1 := by
  have := conj_pow (a := g⁻¹) (b := η) (i := n)
  simpa [hη] using this

end Conj

theorem odd_two_pow_sub_one {e : ℕ} (he : e ≠ 0) : Odd (2 ^ e - 1) := by
  obtain ⟨k, hk⟩ := dvd_pow_self 2 he
  have hpos : 0 < 2 ^ e := by positivity
  exact ⟨k - 1, by omega⟩

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  (h : G0Core G L₁ L₂ V W Z Z₂ e)

include h

theorem dualBase : DualBase h := by
  obtain ⟨y, A, hb⟩ := h.exists_baseData
  obtain ⟨D⟩ := h.pair.side₁.nat
  obtain ⟨fr⟩ := h.pair.side₁.exists_frame D
  obtain ⟨t, ht0, ht1⟩ := h.pair.exists_ne_zero_one
  obtain ⟨η, s, hηK, hsK, hηw, hηy, hsw, hsy⟩ := hb.torus.exists_eta D fr ht0
  have hηL : η ∈ L₁ := (Subgroup.mem_inf.1 hηK).1
  have hsL : s ∈ L₁ := (Subgroup.mem_inf.1 hsK).1
  have he : EtaSpec h D fr t η := ⟨ht0, ht1, hηL, hηw, hηy⟩
  have hηq : η ^ (2 ^ e - 1) = 1 := he.pow_card_sub_one hb.torus.toTorus₀ hηK
  have hss : s * s = 1 := hb.torus.swap_sq hsK hsw hsy
  have hsη : s * η * s = η⁻¹ := hb.torus.swap_conj he hηK hsK hsw hsy
  have hAs : cs A s ≠ A := hb.swap_ne hsL hss hsw hsy
  have hsup : A ⊔ cs A s = L₁ ⊓ Subgroup.centralizer ({y} : Set G) := hb.sup_eq hsK hAs
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  obtain ⟨g₀, hg₀⟩ := hb.kdata.A_mem
  obtain ⟨g, hgW, hgA'⟩ := h.exists_normalizer_of_cs_le_W (g := g₀) (by
    rw [show cs Z g₀ = A from hg₀]
    exact hb.A_le_W)
  have hgA : cs Z g = A := hgA'.symm.trans hg₀
  have hηy' : η * y = y * η :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hηK).2
  have hηA : η ∈ Subgroup.normalizer (A : Set G) := hb.normalizer_A he.normalizer_W hηy'
  have hηZ : ∀ z ∈ Z, η * z * η⁻¹ = z := fun z hz => by
    have hc := Subgroup.mem_centralizer_iff.1 (h.pair.side₁.Z_cent hz) η hηL
    rw [hc]
    group
  obtain ⟨et, het⟩ : ∃ et : G, et = g⁻¹ * η * g := ⟨_, rfl⟩
  have hetZ : cs Z et = Z := by
    rw [het]
    exact cs_conj_normalizes (by rw [hgA]; exact hηA)
  have hetM : et ∈ Subgroup.normalizer (V : Set G) := by
    have := mem_normalizer_of_cs_eq hetZ
    rwa [h.normalizer_Z_eq] at this
  have hetNZ : et ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G) :=
    ⟨hetM, mem_normalizer_of_cs_eq hetZ⟩
  have hetL : et ∈ Subgroup.normalizer (L₁ : Set G) := h.M_le_normalizer_L hetM
  have hetq : et ^ (2 ^ e - 1) = 1 := by
    rw [het]
    exact conj_pow_eq_one hηq
  have hZmem : Z ∈ zClass Z := ⟨1, cs_one Z⟩
  have hZ' : cs Z g⁻¹ ∈ cliq Z W := by
    refine ⟨cs_mem_zClass hZmem g⁻¹, ?_, ?_⟩
    · intro hcZ
      have h1 : g⁻¹ ∈ Subgroup.normalizer (Z : Set G) := mem_normalizer_of_cs_eq hcZ
      have h2 : g ∈ Subgroup.normalizer (Z : Set G) := by simpa using inv_mem h1
      exact hb.ne_Z (hgA.symm.trans (cs_of_mem_normalizer h2))
    · exact (cs_mono h.Z_le_W g⁻¹).trans (cs_of_mem_normalizer (inv_mem hgW)).le
  have hcentZ' : ∀ x ∈ cs Z g⁻¹, et * x * et⁻¹ = x := fun x hx => by
    rw [het]
    exact cs_conj_centralizes hηZ hx
  have hcentZ : ∀ z ∈ Z, et * z * et⁻¹ = z → z = 1 := by
    intro z hz hfix
    have haA : g * z * g⁻¹ ∈ A := by
      have := conj_mem_cs g hz
      rwa [hgA] at this
    have hzet : z * et = et * z := by
      calc z * et = (et * z * et⁻¹) * et := by rw [hfix]
        _ = et * z := by group
    have hcomm : (g * z * g⁻¹) * η = η * (g * z * g⁻¹) := by
      rw [het] at hzet
      calc (g * z * g⁻¹) * η = g * (z * (g⁻¹ * η * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * η * g) * z) * g⁻¹ := by rw [hzet]
        _ = η * (g * z * g⁻¹) := by group
    have h1 := hb.cent_eta he haA hcomm
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hw₀ : D.κ fr.n₀ ≠ 0 := D.κ_ne_zero fr.hn₀.1 fr.hn₀Z
  have hcent : ∀ u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e),
      (u : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ fr.n₀ = D.κ fr.n₀ →
        ∃ p ∈ L₁, D.ρ p = u ∧ et * p * et⁻¹ = p := by
    intro u hu
    obtain ⟨p, hp, hpu⟩ := h.exists_mem_cliq_rho D fr hZ' hu
    exact ⟨p, h.J_le_L (Subgroup.mem_sup_right (hZ'.2.2 hp)), hpu, hcentZ' p hp⟩
  obtain ⟨a, ha0, hact⟩ := scalar_of_odd_cent_sylow D hetL hetNZ
    (odd_two_pow_sub_one h.pair.side₁.e_ne_zero) hetq hw₀ hcent
  obtain ⟨ht₀, -⟩ := h.torus₀_of_scalar D hetM ha0 hact hcentZ
  obtain ⟨φt⟩ := ht₀.nonempty_kEquiv D
  have hZ'Kt : cs Z g⁻¹ ≤ L₁ ⊓ Subgroup.centralizer ({et} : Set G) := fun x hx =>
    Subgroup.mem_inf.2 ⟨h.J_le_L (Subgroup.mem_sup_right (hZ'.2.2 hx)),
      Subgroup.mem_centralizer_singleton_iff.2 (by
        calc x * et = (et * x * et⁻¹) * et := by rw [hcentZ' x hx]
          _ = et * x := by group)⟩
  obtain ⟨I, hI⟩ : ∃ I : Subgroup G, I = cs (L₁ ⊓ Subgroup.centralizer ({et} : Set G)) g :=
    ⟨_, rfl⟩
  have hZI : Z ≤ I := by
    have := cs_mono hZ'Kt g
    rw [cs_inv_cs] at this
    rwa [hI]
  let φI : ↥I ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e) :=
    (MulEquiv.subgroupCongr hI).trans
      ((csIso (L₁ ⊓ Subgroup.centralizer ({et} : Set G)) g).symm.trans φt)
  have hIH : I ≤ Subgroup.centralizer ({η} : Set G) := by
    intro i hi
    rw [hI] at hi
    have hi' : g⁻¹ * i * g ∈ L₁ ⊓ Subgroup.centralizer ({et} : Set G) := mem_cs.1 hi
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hi').2
    rw [het] at hc
    apply Subgroup.mem_centralizer_singleton_iff.2
    calc i * η = g * ((g⁻¹ * i * g) * (g⁻¹ * η * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * η * g) * (g⁻¹ * i * g)) * g⁻¹ := by rw [hc]
      _ = η * i := by group
  have hZH : Z ≤ Subgroup.centralizer ({η} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.2 (by
      have := hηZ z hz
      calc z * η = (η * z * η⁻¹) * η := by rw [this]
        _ = η * z := by group)
  have hsyl : IsSylowOf 2 Z (Subgroup.centralizer ({η} : Set G)) :=
    isSylowOf_of_mem_normalizer hZH h.elemAb2_Z.isPGroup (fun x hxH hxN hx2 => by
      have hxM : x ∈ Subgroup.normalizer (V : Set G) := by rwa [← h.normalizer_Z_eq]
      have hxL : x ∈ L₁ := h.mem_L_of_two_elt hxM hx2
      have hxc : x * η = η * x := Subgroup.mem_centralizer_singleton_iff.1 hxH
      obtain ⟨k, hk⟩ := hx2
      have hxV : x ∈ V := he.two_elt hxL hxc hk
      exact he.cent_V hxV (by rw [← hxc]; group))
  have hTI : CFSG.Open.fusionIsTI Z := fun g' hg' => by
    by_contra hne
    exact hg' (h.side₁.ti g' hne)
  have hZel : CFSG.Open.IsElemAbelian 2 Z :=
    ⟨⟨⟨fun a b => Subtype.ext (h.elemAb2_Z a a.2 b b.2).1⟩⟩, fun x hx => by
      rw [pow_two]
      exact (h.elemAb2_Z x hx x hx).2⟩
  have hBS := oTwoPrime_eq_of_tiSylow h.two_le hZel h.card_Z hsyl hTI hIH hZI ⟨φI⟩
  have hη'' : η = s * η⁻¹ * s⁻¹ := by
    have h1 : s * η * s⁻¹ = η⁻¹ := by rw [hsi]; exact hsη
    calc η = (η⁻¹)⁻¹ := (inv_inv η).symm
      _ = (s * η * s⁻¹)⁻¹ := by rw [h1]
      _ = s * η⁻¹ * s⁻¹ := by group
  have hsI : ∀ i ∈ I, s * i * s⁻¹ ∈ I := by
    have hcl : Subgroup.closure {x : G | x ∈ Subgroup.centralizer ({η} : Set G) ∧
        ∃ k : ℕ, x ^ 2 ^ k = 1} ≤ I.comap (MulAut.conj s).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro x ⟨hxH, k, hk⟩
      show s * x * s⁻¹ ∈ I
      rw [← hBS]
      apply Subgroup.subset_closure
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, k, ?_⟩
      · have hxc : x * η = η * x := Subgroup.mem_centralizer_singleton_iff.1 hxH
        have hxc' : x * η⁻¹ = η⁻¹ * x := (Commute.inv_right (show Commute x η from hxc)).eq
        calc s * x * s⁻¹ * η = s * x * s⁻¹ * (s * η⁻¹ * s⁻¹) := by rw [← hη'']
          _ = s * (x * η⁻¹) * s⁻¹ := by group
          _ = s * (η⁻¹ * x) * s⁻¹ := by rw [hxc']
          _ = (s * η⁻¹ * s⁻¹) * (s * x * s⁻¹) := by group
          _ = η * (s * x * s⁻¹) := by rw [← hη'']
      · have := conj_pow (a := s) (b := x) (i := 2 ^ k)
        rw [this, hk]
        group
    intro i hi
    rw [← hBS] at hi
    exact hcl hi
  have hIA : ∀ i ∈ I, ∀ a ∈ A, i * a = a * i := by
    intro i hi a ha
    rw [← hgA] at ha
    rw [hI] at hi
    have hz : g⁻¹ * a * g ∈ Z := mem_cs.1 ha
    have hi' : g⁻¹ * i * g ∈ L₁ ⊓ Subgroup.centralizer ({et} : Set G) := mem_cs.1 hi
    have hcZ := Subgroup.mem_centralizer_iff.1 (h.pair.side₁.Z_cent hz) _
      (Subgroup.mem_inf.1 hi').1
    calc i * a = g * ((g⁻¹ * i * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * (g⁻¹ * i * g)) * g⁻¹ := by rw [hcZ]
      _ = a * i := by group
  have hIA' : ∀ i ∈ I, ∀ a ∈ cs A s, i * a = a * i := by
    intro i hi a ha
    have ha' : s⁻¹ * a * s ∈ A := mem_cs.1 ha
    have hi' : s⁻¹ * i * s ∈ I := by
      rw [show s⁻¹ * i * s = s * i * s⁻¹ by rw [hsi]]
      exact hsI i hi
    have hc := hIA _ hi' _ ha'
    calc i * a = s * ((s⁻¹ * i * s) * (s⁻¹ * a * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * a * s) * (s⁻¹ * i * s)) * s⁻¹ := by rw [hc]
      _ = a * i := by group
  have hKI : L₁ ⊓ Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer (I : Set G) := by
    rw [← hsup]
    refine sup_le ?_ ?_
    · intro a ha i hi
      exact hIA i hi a ha
    · intro a ha i hi
      exact hIA' i hi a ha
  refine ⟨_, A, I, hb.kdata, ⟨φI⟩, ?_, ?_⟩
  · intro k hk i hi
    exact (Subgroup.mem_centralizer_iff.1 (hKI hk) i hi).symm
  · intro P hPI hPc
    obtain ⟨k, -, hk⟩ := sylow_conj φI h.two_le hZI hPI h.card_Z hPc
    exact ⟨k, hk.symm⟩

end G0Core

end CFSG.CGT.PushingUpLit.A78G0
