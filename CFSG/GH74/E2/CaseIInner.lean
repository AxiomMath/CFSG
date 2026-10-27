module

public import CFSG.GH74.E2.CaseIGlue
public import CFSG.GH74.E2.IsolationProd
public import CFSG.GH74.E2.DtSylow
public import CFSG.GH74.E2.LocalComp

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.GH74.GLS

structure SD16Tables (K : Type) [Group K] [Finite K] : Prop where
  one_class : ∀ u v : K, orderOf u = 2 → orderOf v = 2 → ∃ g : K, g * u * g⁻¹ = v
  sylow : ∀ T : Sylow 2 K, Nonempty (↥(T : Subgroup K) ≃* CFSG.Open.SemidihedralGroup 4)

theorem Qt_commute_comp {G : Type} [Group G] [Finite G] (hH : Hyp G) {t : G}
    (ht : orderOf t = 2) {K : Subgroup G} (hK : IsCompCen t K)
    (huniq : ∀ K' : Subgroup G, IsCompCen t K' → K' = K) :
    ∀ q ∈ Qt t, ∀ k ∈ K, q * k = k * q := by
  have huniq' : ∀ K₁ K₂ : Subgroup G, IsCompCen t K₁ → IsCompCen t K₂ → K₁ = K₂ :=
    fun K₁ K₂ h₁ h₂ => (huniq K₁ h₁).trans (huniq K₂ h₂).symm
  have hL := localK_of_component hH ht huniq' hK
  intro q hq k hk
  obtain ⟨hqC, hqp⟩ := mem_Qt.1 hq
  have h := hL.commute ⟨q, hqC⟩ hqp ⟨k, hK.1 hk⟩ hk
  exact congrArg (fun x : ↥(Cen t) => (x : G)) h

theorem inner_split
    {G : Type} [Group G] [Finite G] (hH : Hyp G) {t : G}
    (ht : orderOf t = 2) {K : Subgroup G} (hK : IsCompCen t K)
    (huniq : ∀ K' : Subgroup G, IsCompCen t K' → K' = K) (hcen : Subgroup.center ↥K = ⊥)
    (hinner : ∀ g ∈ Cen t, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹)
    (hQ8 : Nonempty (↥(Qt t) ≃* QuaternionGroup 2)) {c : G} (hc3 : orderOf c = 3)
    (hcC : c ∈ Cen t) (hcK : ∀ k ∈ K, c * k = k * c) {D : Subgroup G}
    (hD : D = Cen t ⊓ Subgroup.centralizer (K : Set G)) :
    ∃ P : Sylow 2 ↥D, D ≤ Cen t ∧ D ≤ Subgroup.centralizer (K : Set G) ∧
      (∀ k ∈ K, ∀ d ∈ D, k * d = d * k) ∧ K ⊓ D = ⊥ ∧ Cen t = K ⊔ D ∧
      t ∈ (P : Subgroup ↥D).map D.subtype ∧
      (Nonempty (↥((P : Subgroup ↥D).map D.subtype) ≃* QuaternionGroup 2) ∨
        Nonempty (↥((P : Subgroup ↥D).map D.subtype) ≃* QuaternionGroup 4) ∨
        Nonempty (↥(P : Subgroup ↥D) ≃* CFSG.Open.SemidihedralGroup 4)) := by
  have huniq' : ∀ K₁ K₂ : Subgroup G, IsCompCen t K₁ → IsCompCen t K₂ → K₁ = K₂ :=
    fun K₁ K₂ h₁ h₂ => (huniq K₁ h₁).trans (huniq K₂ h₂).symm
  have hL := localK_of_component hH ht huniq' hK
  subst hD
  set D : Subgroup G := Cen t ⊓ Subgroup.centralizer (K : Set G) with hDdef
  have hCKD : Cen t = K ⊔ D := cen_eq_sup_of_inner hK.1 hinner
  have hcomm : ∀ k ∈ K, ∀ d ∈ D, k * d = d * k := fun k hk d hd =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hd).2 k hk
  have hdisj : K ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro x hx
    obtain ⟨hxK, hxD⟩ := Subgroup.mem_inf.1 hx
    have hxc : x ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.1 hxD).2
    have hxz : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc y y.2)
    rw [hcen, Subgroup.mem_bot] at hxz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxz
  have hQD : Qt t ≤ D := fun q hq =>
    Subgroup.mem_inf.2 ⟨Qt_le_Cen t hq, Subgroup.mem_centralizer_iff.2 fun k hk =>
      (Qt_commute_comp hH ht hK huniq q hq k hk).symm⟩
  let Q' : Subgroup ↥D := (Qt t).subgroupOf D
  have hQ'n : Q'.Normal := ⟨fun n hn g =>
    Qt_conj_mem t (Subgroup.mem_inf.1 g.2).1 hn⟩
  have hC' : ∀ d : ↥D, (∀ q ∈ Q', d * q = q * d) → d ∈ Q' := by
    intro d hd
    have hdC : (d : G) ∈ Cen t := (Subgroup.mem_inf.1 d.2).1
    have hdK : (d : G) ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.1 d.2).2
    let d' : ↥(Cen t) := ⟨d, hdC⟩
    have h1 : ∀ q ∈ CFSG.pCore 2 ↥(Cen t), d' * q = q * d' := by
      intro q hq
      have hqQ : ((q : ↥(Cen t)) : G) ∈ Qt t := ⟨q, hq, rfl⟩
      have h := hd ⟨(q : G), hQD hqQ⟩ hqQ
      exact Subtype.ext (congrArg (fun x : ↥D => (x : G)) h)
    have h2 : ∀ k ∈ K.subgroupOf (Cen t), d' * k = k * d' := by
      intro k hk
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hdK k hk).symm
    have h3 := hL.self_centralizing d' h1 h2
    exact ⟨d', h3, rfl⟩
  have h3 : 3 ∣ Nat.card ↥D := by
    have hcD : c ∈ D := Subgroup.mem_inf.2
      ⟨hcC, Subgroup.mem_centralizer_iff.2 (fun k hk => (hcK k hk).symm)⟩
    have : orderOf (⟨c, hcD⟩ : ↥D) = 3 := by rw [← Subgroup.orderOf_coe]; exact hc3
    rw [← this]
    exact orderOf_dvd_natCard _
  have hQ' : Nonempty (↥Q' ≃* QuaternionGroup 2) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hQD).trans hQ8.some⟩
  have hQp' : IsPGroup 2 ↥Q' :=
    (Qt_isPGroup t).of_equiv (Subgroup.subgroupOfEquivOfLe hQD).symm
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥D) := inferInstance
  have hQ'P : Q' ≤ (P : Subgroup ↥D) := hQp'.le_sylow_of_normal P
  have htD : t ∈ D := hQD (t_mem_Qt ht)
  have htSD : t ∈ (P : Subgroup ↥D).map D.subtype :=
    ⟨⟨t, htD⟩, hQ'P (t_mem_Qt ht), rfl⟩
  refine ⟨P, inf_le_left, inf_le_right, hcomm, hdisj, hCKD, htSD, ?_⟩
  rcases sylow_two_of_Dt Q' hQ' hC' h3 P with ⟨-, hPQ⟩ | ⟨-, hQ16⟩ | ⟨-, hSD⟩
  · exact Or.inl ⟨(sylowMapEquiv D P).symm.trans ((MulEquiv.subgroupCongr hPQ).trans hQ'.some)⟩
  · exact Or.inr (Or.inl ⟨(sylowMapEquiv D P).symm.trans hQ16.some⟩)
  · exact Or.inr (Or.inr hSD)

theorem inner_two_core
    {G : Type} [Group G] [Finite G] (hH : Hyp G) {t : G}
    (ht : orderOf t = 2) {K : Subgroup G} (hK : IsCompCen t K)
    (huniq : ∀ K' : Subgroup G, IsCompCen t K' → K' = K) (hcen : Subgroup.center ↥K = ⊥)
    (hT : SD16Tables ↥K)
    (hinner : ∀ g ∈ Cen t, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹)
    (hQ8 : Nonempty (↥(Qt t) ≃* QuaternionGroup 2)) {c : G} (hc3 : orderOf c = 3)
    (hcC : c ∈ Cen t) (hcK : ∀ k ∈ K, c * k = k * c)
    (hnotSD : ∀ P : Sylow 2 ↥(Cen t ⊓ Subgroup.centralizer (K : Set G)),
      ¬ Nonempty (↥(P : Subgroup ↥(Cen t ⊓ Subgroup.centralizer (K : Set G))) ≃*
        CFSG.Open.SemidihedralGroup 4)) : False := by
  obtain ⟨P, hDC, -, hcomm, hdisj, hCKD, htSD, hcases⟩ :=
    inner_split hH ht hK huniq hcen hinner hQ8 hc3 hcC hcK rfl
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hone : ∀ u ∈ K, ∀ v ∈ K, orderOf u = 2 → orderOf v = 2 → ∃ g ∈ K, g * u * g⁻¹ = v := by
    intro u hu v hv hou hov
    obtain ⟨g, hg⟩ := hT.one_class ⟨u, hu⟩ ⟨v, hv⟩
      (by rw [← Subgroup.orderOf_coe]; exact hou) (by rw [← Subgroup.orderOf_coe]; exact hov)
    exact ⟨g, g.2, congrArg Subtype.val hg⟩
  let eK : ↥((T : Subgroup ↥K).map K.subtype) ≃* SD16M :=
    (sylowMapEquiv K T).symm.trans
      ((hT.sylow T).some.trans (CFSG.Semidihedral.presentationEquivModel 4 (by norm_num)))
  rcases hcases with hQ8' | hQ16' | hSD
  · exact isolation_direct_product hH.simple hH.nonabelian ht K _ hK.1 hDC hcomm hdisj
      hCKD hone _ (sylow_map_le K T) (sylow_map_isPGroup K T) (sylow_map_max K T) _
      (sylow_map_le _ P) (sylow_map_isPGroup _ P) (sylow_map_max _ P) htSD eK 2 (Or.inl rfl)
      hQ8'.some
  · exact isolation_direct_product hH.simple hH.nonabelian ht K _ hK.1 hDC hcomm hdisj
      hCKD hone _ (sylow_map_le K T) (sylow_map_isPGroup K T) (sylow_map_max K T) _
      (sylow_map_le _ P) (sylow_map_isPGroup _ P) (sylow_map_max _ P) htSD eK 4 (Or.inr rfl)
      hQ16'.some
  · exact hnotSD P hSD

end CFSG.GH74.E2
