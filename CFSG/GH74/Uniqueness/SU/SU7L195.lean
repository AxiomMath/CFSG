module

public import CFSG.GH74.Uniqueness.SU.SU7L194
public import CFSG.GH74.Uniqueness.SU.SU7L192c
public import CFSG.Fischer.Aut.Generate
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG

namespace L195

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

section Bar

variable {G : Type} [Group G]

theorem card_dvd_cent_bar {M : Subgroup G} (hO : pPrimeCore 2 ↥M = ⊥) {x : G} (hx : x ∈ M)
    (D : Subgroup (Mbar M)) (hD : ∀ d ∈ D, d * xbar M x hx = xbar M x hx * d) :
    Nat.card D ∣ Nat.card ↥(centralizer ({x} : Set G)) := by
  set φ : ↥M →* Mbar M := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hφ
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφ, QuotientGroup.ker_mk', hO]
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  set D₀ : Subgroup ↥M := D.comap φ with hD₀
  have h1 : D₀.map φ = D := Subgroup.map_comap_eq_self_of_surjective hsurj D
  have h2 : Nat.card D = Nat.card D₀ := by
    have := Subgroup.card_map_of_injective (K := D₀) hinj
    rw [h1] at this
    exact this
  have h3 : D₀.map M.subtype ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have h4 : φ d * φ ⟨x, hx⟩ = φ ⟨x, hx⟩ * φ d := hD (φ d) hd
    rw [← map_mul, ← map_mul] at h4
    have h6 := congrArg Subtype.val (hinj h4)
    simpa using h6.symm
  have h4 : Nat.card (D₀.map M.subtype) = Nat.card D₀ :=
    Subgroup.card_map_of_injective M.subtype_injective
  rw [h2, ← h4]
  exact Subgroup.card_dvd_of_le h3

theorem fstar_eq_of_bar {M T : Subgroup G} (hO : pPrimeCore 2 ↥M = ⊥)
    (hb : barImage M T = generalizedFitting (Mbar M)) :
    generalizedFitting ↥M = T.subgroupOf M := by
  set φ : ↥M →* Mbar M := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hφ
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφ, QuotientGroup.ker_mk', hO]
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  let e : ↥M ≃* Mbar M := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have h1 := CFSG.QuasithinUnique.Setup.Layer.Actor.generalizedFitting_map e
  have he : e.toMonoidHom = φ := MonoidHom.ext fun _ => rfl
  rw [he] at h1
  rw [← hb] at h1
  have h2 : (generalizedFitting ↥M).map φ = (T.subgroupOf M).map φ := h1
  exact Subgroup.map_injective hinj h2

end Bar

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem card_cent_z (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    Nat.card ↥(centralizer ({z} : Set G)) = 1920 := by
  classical
  set C : Subgroup G := centralizer ({z} : Set G) with hCdef
  obtain ⟨ψ, hψ, hker, -⟩ := L192.exists_surj_alt5_G hKI3 hKI4 hc
  have hOC : pPrimeCore 2 ↥C = ⊥ :=
    (L194.lemma194_of_ctx hKI3 hKI4 hc).2 z (Base.z_mem_S hc.conf) hc.conf.hz
  have hSC : (S : Subgroup G) ≤ C := fun s hs =>
    mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hc.conf.z_center s hs).symm)
  have hRC : R ≤ C := hc.c19.R_le.trans hSC
  rw [hOC, sup_bot_eq] at hker
  have hR32 : Nat.card ↥(R.subgroupOf C) = 32 := by
    rw [← (RF.R_facts hc).1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, card_alt5, hker,
    hR32] at h1
  exact h1.trans (by norm_num)

theorem exists_conj_z_of_ST (hc : Ctx19 S U M V x z A B R) {s : G} (hsS : s ∈ (S : Subgroup G))
    (hsT : s ∉ Tsub S U) (hs2 : orderOf s = 2) : ∃ g : G, g * z * g⁻¹ = s := by
  obtain ⟨u₀, hu₀U, hu₀1, hu₀z⟩ := RF.exists_u₀ hc
  obtain ⟨g₂, -, hg₂⟩ := lemma191 G S U M V x z A B R hc s hsS hsT hs2 u₀ hu₀U hu₀1 hu₀z
  obtain ⟨h, -, hh⟩ := Tr.exists_conj_z hc.hyp hc.conf hc.concl hu₀U hu₀1
  refine ⟨g₂ * h, ?_⟩
  calc g₂ * h * z * (g₂ * h)⁻¹ = g₂ * (h * z * h⁻¹) * g₂⁻¹ := by group
    _ = g₂ * u₀ * g₂⁻¹ := by rw [hh]
    _ = s := by rw [← hg₂]; group

theorem exists_conj_zx (hc : Ctx19 S U M V x z A B R) : ∃ g : G, g * z * g⁻¹ = x :=
  exists_conj_z_of_ST hc (Base.x_mem_S hc.conf)
    (Base.j2facts hc.hyp hc.conf hc.concl).x_not_mem hc.conf.hx

theorem not_nine_dvd (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    ¬ 9 ∣ Nat.card ↥(centralizer ({xbar M x hc.conf.x_mem} : Set (Mbar M)) ⊓
      generalizedFitting (Mbar M)) := by
  intro h9
  have hO : pPrimeCore 2 ↥M = ⊥ := (L194.lemma194_of_ctx hKI3 hKI4 hc).1
  have hd := card_dvd_cent_bar hO hc.conf.x_mem
    (centralizer ({xbar M x hc.conf.x_mem} : Set (Mbar M)) ⊓ generalizedFitting (Mbar M))
    (fun d hd => (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hd).1 _ (Set.mem_singleton _)).symm)
  obtain ⟨g, hg⟩ := exists_conj_zx hc
  have h1 : Nat.card ↥(centralizer ({x} : Set G)) = 1920 := by
    rw [← hg, CFSG.Fischer.card_centralizer_conj g z]
    exact card_cent_z hKI3 hKI4 hc
  rw [h1] at hd
  have h2 := h9.trans hd
  omega

theorem cent_le_T (hc : Ctx19 S U M V x z A B R)
    (hF : generalizedFitting ↥M = (Tsub S U).subgroupOf M) :
    centralizer ((Tsub S U : Subgroup G) : Set G) ≤ Tsub S U := by
  intro c hcT
  have hcN : c ∈ normalizer ((Tsub S U : Subgroup G) : Set G) :=
    Gen.mem_normalizer_of_conj_le (fun t ht => by
      have h1 : t * c = c * t := mem_centralizer_iff.1 hcT t ht
      have : c * t * c⁻¹ = t := by
        calc c * t * c⁻¹ = (t * c) * c⁻¹ := by rw [h1]
          _ = t := by group
      rw [this]; exact ht)
  have hcM : c ∈ M := L192.normalizer_T_le_M hc hcN
  have hcent : (⟨c, hcM⟩ : ↥M) ∈ centralizer ((generalizedFitting ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [mem_centralizer_iff]
    intro f hf
    rw [SetLike.mem_coe, hF] at hf
    exact Subtype.ext (mem_centralizer_iff.1 hcT (f : G) hf)
  have hcF := CFSG.centralizer_generalizedFitting_le ↥M hcent
  rw [hF] at hcF
  exact hcF

theorem normalizer_eq (hc : Ctx19 S U M V x z A B R)
    (hF : generalizedFitting ↥M = (Tsub S U).subgroupOf M) :
    normalizer ((Tsub S U : Subgroup G) : Set G) = M := by
  apply le_antisymm
  · intro n hn
    exact L192.normalizer_T_le_M hc hn
  · intro m hm
    have hnorm : ((Tsub S U).subgroupOf M).Normal := hF ▸ Gen.normal_generalizedFitting ↥M
    apply Gen.mem_normalizer_of_conj_le
    intro t ht
    have htM : t ∈ M := hc.conf.S_le (Base.T_le_S ht)
    exact hnorm.conj_mem ⟨t, htM⟩ ht ⟨m, hm⟩

end L195

theorem cor195 (hKI3 : K.KI3) (hKI4 : K.KI4) : Cor195Stmt := by
  intro G _ _ S U M V x z A B R hc
  classical
  have hO : pPrimeCore 2 ↥M = ⊥ := (L194.lemma194_of_ctx hKI3 hKI4 hc).1
  have hb : barImage M (Tsub S U) = generalizedFitting (Mbar M) := by
    rcases hc.concl.case with ⟨-, -, h9⟩ | hb
    · exact absurd h9 (L195.not_nine_dvd hKI3 hKI4 hc)
    · exact hb
  have hF : generalizedFitting ↥M = (Tsub S U).subgroupOf M := L195.fstar_eq_of_bar hO hb
  refine ⟨hF, ?_⟩
  have hMN := L195.normalizer_eq hc hF
  have hTC : Tsub S U ⊔ centralizer ((Tsub S U : Subgroup G) : Set G) = Tsub S U :=
    sup_eq_left.2 (L195.cent_le_T hc hF)
  have h := L192.lemma192_c hKI3 hKI4 hc
  rw [← hMN]
  rw [hTC] at h
  exact h

namespace L195

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem fstar_eq_T (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    generalizedFitting ↥M = (Tsub S U).subgroupOf M :=
  (cor195 hKI3 hKI4 G S U M V x z A B R hc).1

theorem normalizes_T (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U := by
  intro m hm t ht
  have hMN := normalizer_eq hc (fstar_eq_T hKI3 hKI4 hc)
  have hmN : m ∈ normalizer ((Tsub S U : Subgroup G) : Set G) := by rw [hMN]; exact hm
  exact (mem_normalizer_iff.1 hmN t).1 ht

theorem cent_M_le_T (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U := by
  intro m _ hcomm
  have hmC : m ∈ centralizer ((Tsub S U : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact (hcomm t ht).symm
  exact cent_le_T hc (fstar_eq_T hKI3 hKI4 hc) hmC

theorem card_M (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    Nat.card M = 1152 := by
  obtain ⟨-, hnorm, ⟨e⟩⟩ := cor195 hKI3 hKI4 G S U M V x z A B R hc
  have hJ := Base.j2facts hc.hyp hc.conf hc.concl
  have hTM : Tsub S U ≤ M := Base.T_le_S.trans hc.conf.S_le
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Tsub S U).subgroupOf M)
  have h2 : Nat.card ↥((Tsub S U).subgroupOf M) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv]; exact hJ.card_T
  have h3 : Nat.card (↥M ⧸ (Tsub S U).subgroupOf M) = 18 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]; simp [Nat.factorial]
    have h7 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_eq_fintype_card]; simp
    rw [h6, h7]
  rw [h2, h3] at h1
  omega

end L195

end CFSG.GH74.Uniqueness.SU.SU7
