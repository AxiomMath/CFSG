module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma620C
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Syl

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

namespace I13HRank

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G}

omit [Finite G] in
theorem mem_map_conj_inv {A : Subgroup G} {g y : G} :
    y ∈ A.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : g * (MulAut.conj g⁻¹).toMonoidHom u * g⁻¹ = u := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group
    rw [this]; exact hu
  · intro hy
    refine ⟨g * y * g⁻¹, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group

omit [Finite G] in
theorem card_map_conj_inv (A : Subgroup G) (g : G) :
    Nat.card ↥(A.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

omit [Finite G] in
theorem isPGroup_two_of_sq {A : Subgroup G} (hA2 : ∀ a ∈ A, a * a = 1) : IsPGroup 2 A := by
  intro a
  refine ⟨1, Subtype.ext ?_⟩
  simpa [pow_two] using hA2 a a.2

omit [Finite G] in
theorem comm_of_sq {A : Subgroup G} (hA2 : ∀ a ∈ A, a * a = 1) {u v : G} (hu : u ∈ A)
    (hv : v ∈ A) : u * v = v * u := by
  have h1 : (u * v) * (u * v) = 1 := hA2 _ (mul_mem hu hv)
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hA2 u hu)
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hA2 v hv)
  calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
    _ = v * u := by rw [hu', hv']

variable (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem card_T0_le : Nat.card T₀ ≤ 128 := by
  have hcfg := h.conf.cfg
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hcfg.T₀_pgroup
  have hle : T₀ ≤ L ⊓ centralizer ({t} : Set G) :=
    le_inf hcfg.T₀_le (fun y hy => mem_centralizer_singleton_iff.2 (hcfg.t_central y hy))
  have hdvd : Nat.card T₀ ∣ 1920 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [h.wf.card_cent] at this
  have hk7 : k ≤ 7 := by
    by_contra hk8
    have h256 : 2 ^ 8 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := h256.trans (hk ▸ hdvd)
    norm_num at this
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk7
    _ = 128 := by norm_num

theorem card_le_four_of_le_E {U : Subgroup G} (hUE : U ≤ E) (hU2 : ∀ a ∈ U, a * a = 1) :
    Nat.card U ≤ 4 := by
  have hcfg := h.conf.cfg
  have hEle : E ≤ T₀ := h.conf.econfig.le
  have htE : t ∈ E := h.t_mem_E
  have ht2 : t * t = 1 := h.t_sq
  have ht1 : t ≠ 1 := h.t_ne
  have hcommt : ∀ y ∈ E, y * t = t * y := fun y hy => hcfg.t_central y (hEle hy)
  by_cases hall : ∀ u ∈ U, u = 1 ∨ u = t
  · have hsub : (U : Set G) ⊆ {1, t} := fun u hu => by simpa using hall u hu
    have h2 : Set.ncard ({1, t} : Set G) ≤ 2 := by
      have := Set.ncard_insert_le (1 : G) ({t} : Set G)
      rw [Set.ncard_singleton] at this
      omega
    calc Nat.card U = Set.ncard (U : Set G) := Nat.card_coe_set_eq (U : Set G)
      _ ≤ Set.ncard ({1, t} : Set G) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 4 := by omega
  · push Not at hall
    obtain ⟨x, hxU, hx1, hxt⟩ := hall
    have hxE : x ∈ E := hUE hxU
    have hx2 : x * x = 1 := hU2 x hxU
    have hcomm : x * t = t * x := hcommt x hxE
    set C : Set G := {y | y ∈ E ∧ y * y = 1 ∧ y ≠ 1 ∧ y ≠ t ∧ y * x = x * y} with hC
    set A8 : Set G := {y | y ∈ E ∧ y * y = 1 ∧ y ≠ 1 ∧ y ≠ t ∧ y * x ≠ x * y} with hA8
    have h10 := h.ef.card_two
    have h8 : A8.ncard = 8 := h.ef.anti_two x hxE hx2 hx1 hxt
    have hCle : C.ncard ≤ 2 := by
      have hdisj : Disjoint C A8 :=
        Set.disjoint_left.2 fun y hyC hyA => hyA.2.2.2.2 hyC.2.2.2.2
      have hsub : C ∪ A8 ⊆ {e : G | e ∈ E ∧ e * e = 1 ∧ e ≠ 1 ∧ e ≠ t} := by
        rintro y (⟨he, h1, h2, h3, -⟩ | ⟨he, h1, h2, h3, -⟩) <;> exact ⟨he, h1, h2, h3⟩
      have h1 := Set.ncard_union_eq hdisj (Set.toFinite C) (Set.toFinite A8)
      have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
    have hxC : x ∈ C := ⟨hxE, hx2, hx1, hxt, rfl⟩
    have hxtx : x * t ∈ C := by
      have hsq : (x * t) * (x * t) = 1 := by
        calc (x * t) * (x * t) = x * (t * x) * t := by group
          _ = x * (x * t) * t := by rw [← hcomm]
          _ = (x * x) * (t * t) := by group
          _ = 1 := by rw [hx2, ht2, one_mul]
      refine ⟨mul_mem hxE htE, hsq, fun h1 => hxt ?_, fun h1 => hx1 ?_, ?_⟩
      · calc x = x * (t * t) := by rw [ht2, mul_one]
          _ = (x * t) * t := by group
          _ = t := by rw [h1, one_mul]
      · exact mul_right_cancel (show x * t = 1 * t by rw [one_mul]; exact h1)
      · calc (x * t) * x = x * (t * x) := by group
          _ = x * (x * t) := by rw [← hcomm]
    have hne : x ≠ x * t := fun h1 =>
      ht1 (mul_left_cancel (a := x) (by rw [mul_one]; exact h1.symm))
    have hpair : Set.ncard ({x, x * t} : Set G) = 2 := Set.ncard_pair hne
    have hCeq : ({x, x * t} : Set G) = C := by
      refine Set.eq_of_subset_of_ncard_le ?_ (by omega) (Set.toFinite _)
      rintro y (rfl | rfl)
      · exact hxC
      · exact hxtx
    have hsub : (U : Set G) ⊆ {1, t, x, x * t} := by
      intro u hu
      by_cases hu1 : u = 1
      · simp [hu1]
      by_cases hut : u = t
      · simp [hut]
      have huC : u ∈ C := ⟨hUE hu, hU2 u hu, hu1, hut, comm_of_sq hU2 hu hxU⟩
      rw [← hCeq] at huC
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huC ⊢
      tauto
    have h4 : Set.ncard ({1, t, x, x * t} : Set G) ≤ 4 := by
      have h1 : ({x * t} : Set G).ncard = 1 := Set.ncard_singleton _
      have h2 := Set.ncard_insert_le x ({x * t} : Set G)
      have h3 := Set.ncard_insert_le t (insert x ({x * t} : Set G))
      have h5 := Set.ncard_insert_le (1 : G) (insert t (insert x ({x * t} : Set G)))
      omega
    calc Nat.card U = Set.ncard (U : Set G) := Nat.card_coe_set_eq (U : Set G)
      _ ≤ Set.ncard ({1, t, x, x * t} : Set G) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 4 := h4

theorem card_le_of_le_T {A : Subgroup G} (hAT : A ≤ T₀ ⊔ zpowers z)
    (hA2 : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 32 := by
  have hcfg := h.conf.cfg
  have hEle : E ≤ T₀ := h.conf.econfig.le
  have hrel : T₀.relIndex (T₀ ⊔ zpowers z) = 2 := hcfg.T₀_relIndex_T
  have h2 : T₀.relIndex A ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right (H := T₀) hAT (by rw [hrel]; norm_num)
    rwa [hrel] at this
  have hA : Nat.card A ≤ 2 * Nat.card ↥(T₀ ⊓ A) := by
    have h1 := Subgroup.relIndex_mul_card (H := T₀) (K := A)
    calc Nat.card A = T₀.relIndex A * Nat.card ↥(T₀ ⊓ A) := h1.symm
      _ ≤ 2 * Nat.card ↥(T₀ ⊓ A) := Nat.mul_le_mul_right _ h2
  have hET : E.relIndex T₀ ≤ 4 := by
    have h1 := Subgroup.relIndex_mul_card (H := E) (K := T₀)
    rw [inf_eq_left.2 hEle, h.wf.card_E] at h1
    have := card_T0_le h
    omega
  have hET0 : E.relIndex T₀ ≠ 0 := by
    have h1 := Subgroup.relIndex_mul_card (H := E) (K := T₀)
    rw [inf_eq_left.2 hEle, h.wf.card_E] at h1
    have hpos : 0 < Nat.card T₀ := Nat.card_pos
    omega
  have hEU : E.relIndex (T₀ ⊓ A) ≤ 4 :=
    (Subgroup.relIndex_le_of_le_right (H := E) inf_le_left hET0).trans hET
  have hU : Nat.card ↥(T₀ ⊓ A) ≤ 4 * Nat.card ↥(E ⊓ (T₀ ⊓ A)) := by
    have h1 := Subgroup.relIndex_mul_card (H := E) (K := T₀ ⊓ A)
    calc Nat.card ↥(T₀ ⊓ A) = E.relIndex (T₀ ⊓ A) * Nat.card ↥(E ⊓ (T₀ ⊓ A)) := h1.symm
      _ ≤ 4 * Nat.card ↥(E ⊓ (T₀ ⊓ A)) := Nat.mul_le_mul_right _ hEU
  have hV : Nat.card ↥(E ⊓ (T₀ ⊓ A)) ≤ 4 :=
    card_le_four_of_le_E h inf_le_left fun a ha => hA2 a ha.2.2
  calc Nat.card A ≤ 2 * Nat.card ↥(T₀ ⊓ A) := hA
    _ ≤ 2 * (4 * 4) := Nat.mul_le_mul_left _ (hU.trans (Nat.mul_le_mul_left _ hV))
    _ = 32 := by norm_num

theorem card_le_of_le_cent_z {A : Subgroup G} (hAC : A ≤ centralizer ({z} : Set G))
    (hA2 : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 32 := by
  have hcfg := h.conf.cfg
  set Θ := centralizer ({z} : Set G) with hΘ
  have hTΘ : T₀ ⊔ zpowers z ≤ Θ :=
    sup_le (fun a ha => mem_centralizer_singleton_iff.2 (hcfg.z_comm_of_mem_A (hcfg.T₀_le ha)))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hTp : IsPGroup 2 (T₀ ⊔ zpowers z : Subgroup G) := hcfg.T_pgroup
  have hTcard : Nat.card (T₀ ⊔ zpowers z : Subgroup G) = 2 * Nat.card T₀ := h.card_T0_sup_z
  have hTmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Θ → T₀ ⊔ zpowers z ≤ R →
      R ≤ T₀ ⊔ zpowers z := by
    intro R hR hRΘ hle
    have h1 : Nat.card R ≤ 2 * Nat.card T₀ := h.cent_z_card_le hR hRΘ
    have heq : T₀ ⊔ zpowers z = R := Subgroup.eq_of_le_of_card_ge hle (by omega)
    rw [heq]
  obtain ⟨P, ⟨hP2, hAP, hPΘ⟩, hPmax⟩ :=
    (Set.toFinite {P : Subgroup G | IsPGroup 2 P ∧ A ≤ P ∧ P ≤ Θ}).exists_maximalFor id _
      ⟨A, isPGroup_two_of_sq hA2, le_rfl, hAC⟩
  have hPmax' : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Θ → P ≤ R → R ≤ P :=
    fun R hR hRΘ hle => hPmax ⟨hR, hAP.trans hle, hRΘ⟩ hle
  obtain ⟨g, -, hg⟩ := sylow_conj hTΘ hPΘ hTp hP2 hTmax hPmax'
  have hmem : ∀ y : G, y ∈ A.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ A :=
    fun y => mem_map_conj_inv
  have hle : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ T₀ ⊔ zpowers z := by
    intro y hy
    have hyA := (hmem y).1 hy
    have := (hg _).1 (hAP hyA)
    simpa [mul_assoc] using this
  refine (card_map_conj_inv A g).symm.le.trans (card_le_of_le_T h hle ?_)
  intro y hy
  have h1 := hA2 _ ((hmem y).1 hy)
  calc y * y = g⁻¹ * ((g * y * g⁻¹) * (g * y * g⁻¹)) * g := by group
    _ = 1 := by rw [h1]; group

end I13HRank

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G}

open I13HRank in
theorem rank_cent_conj_le (h : Hyp69 L z t T₀ E Q x β B S) {u : G}
    (hu : ∃ g : G, u = g * z * g⁻¹) {A : Subgroup G} (hA : A ≤ centralizer ({u} : Set G))
    (hA2 : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 32 := by
  obtain ⟨g, rfl⟩ := hu
  have hmem : ∀ y : G, y ∈ A.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ A :=
    fun y => mem_map_conj_inv
  have hC : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({z} : Set G) := by
    intro y hy
    have hcomm := mem_centralizer_singleton_iff.1 (hA ((hmem y).1 hy))
    rw [mem_centralizer_singleton_iff]
    calc y * z = g⁻¹ * ((g * y * g⁻¹) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (g * y * g⁻¹)) * g := by rw [hcomm]
      _ = z * y := by group
  refine (card_map_conj_inv A g).symm.le.trans (card_le_of_le_cent_z h hC ?_)
  intro y hy
  have h1 := hA2 _ ((hmem y).1 hy)
  calc y * y = g⁻¹ * ((g * y * g⁻¹) * (g * y * g⁻¹)) * g := by group
    _ = 1 := by rw [h1]; group

end CFSG.EvenSporadicStandard.Fin76b
