module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Block
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open Subgroup

namespace A3Gen

variable {G : Type*} [Group G]

theorem map_conj_eq_of_mem_normalizer {A : Subgroup G} {h : G}
    (hh : h ∈ normalizer (A : Set G)) : A.map (MulAut.conj h).toMonoidHom = A := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have := Subgroup.mem_normalizer_iff.mp (inv_mem hh) x
  simpa using this.symm

theorem mem_normalizer_of_map_conj_eq {A : Subgroup G} {h : G}
    (hh : A.map (MulAut.conj h).toMonoidHom = A) : h ∈ normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : h * x * h⁻¹ ∈ A ↔ h * x * h⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom := by rw [hh]
  rw [h1, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [show h⁻¹ * (h * x * h⁻¹) * h = x by group]

theorem mem_normalizer_sup {A B : Subgroup G} {h : G} (hA : h ∈ normalizer (A : Set G))
    (hB : h ∈ normalizer (B : Set G)) : h ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB]

theorem relIndex_sup_eq_of_le_normalizer' {A B : Subgroup G}
    (h : A ≤ normalizer (B : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv.symm

theorem card_eq_card_mul_relIndex' [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card K = Nat.card H * H.relIndex K := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
  exact (Subgroup.card_mul_index _).symm

theorem card_sup_mul_card_inf_of_le_normalizer' [Finite G] {A B : Subgroup G}
    (h : A ≤ normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have h1 := card_eq_card_mul_relIndex' (le_sup_right : B ≤ A ⊔ B)
  have h2 := card_eq_card_mul_relIndex' (inf_le_left : A ⊓ B ≤ A)
  have h3 : (A ⊓ B).relIndex A = B.relIndex A := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right B A
  rw [h1, h2, relIndex_sup_eq_of_le_normalizer' h, h3]
  ring

theorem card_H_eq [Finite G] {H S L U : Subgroup G} (hH : H = L ⊔ S)
    (hSL : S ≤ normalizer (L : Set G)) (hS2 : IsPGroup 2 S) (hL12 : Nat.card L = 12)
    (hU4 : Nat.card U = 4) (hUL : U ≤ L) (hUS : U ≤ S) : Nat.card H = 3 * Nat.card S := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer' hSL
  rw [sup_comm, ← hH, inf_comm, hL12] at h1
  have hinf2 : IsPGroup 2 (L ⊓ S : Subgroup G) := hS2.to_le inf_le_right
  obtain ⟨b, hb⟩ := hinf2.exists_card_eq
  have hdvd : Nat.card (L ⊓ S : Subgroup G) ∣ 12 := hL12 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hdvd4 : 4 ∣ Nat.card (L ⊓ S : Subgroup G) :=
    hU4 ▸ Subgroup.card_dvd_of_le (le_inf hUL hUS)
  have hb2 : Nat.card (L ⊓ S : Subgroup G) = 4 := by
    rw [hb] at hdvd hdvd4 ⊢
    have hle : b ≤ 2 := by
      by_contra hcon
      have hcon := not_le.mp hcon
      have : 2 ^ 3 ∣ 2 ^ b := pow_dvd_pow 2 hcon
      have h8 : 8 ∣ 12 := this.trans hdvd
      omega
    have hge : 2 ≤ b := by
      by_contra hcon
      have hcon := not_le.mp hcon
      have : 2 ^ b ≤ 2 := by
        interval_cases b <;> norm_num
      have := Nat.le_of_dvd (by positivity) hdvd4
      omega
    have : b = 2 := le_antisymm hle hge
    rw [this]; norm_num
  rw [hb2] at h1
  omega

theorem mem_centralizer_conj {H L : Subgroup G} (hHL : H ≤ normalizer (L : Set G)) {h : G}
    (hh : h ∈ H) {x : G} (hx : x ∈ centralizer (L : Set G)) :
    h * x * h⁻¹ ∈ centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro l hl
  have hl' : h⁻¹ * l * h ∈ L := by
    have := Subgroup.mem_normalizer_iff.mp (inv_mem (hHL hh)) l
    simpa using this.mp hl
  have := hx _ hl'
  calc l * (h * x * h⁻¹) = h * ((h⁻¹ * l * h) * x) * h⁻¹ := by group
    _ = h * (x * (h⁻¹ * l * h)) * h⁻¹ := by rw [this]
    _ = (h * x * h⁻¹) * l := by group

theorem D_facts [Finite G] {H S L : Subgroup G} (hHL : H ≤ normalizer (L : Set G)) (hLH : L ≤ H)
    (hcardH : Nat.card H = 3 * Nat.card S) (hS2 : IsPGroup 2 S)
    (hL12 : Nat.card L = 12) (hZ : ∀ g ∈ L, (∀ l ∈ L, g * l = l * g) → g = 1)
    (hSyl : ∀ N : Subgroup G, N ≤ H → H ≤ normalizer (N : Set G) → IsPGroup 2 N → N ≤ S) :
    H ≤ normalizer ((H ⊓ centralizer (L : Set G) : Subgroup G) : Set G) ∧
      H ⊓ centralizer (L : Set G) ≤ S ∧ L ⊓ (H ⊓ centralizer (L : Set G)) = ⊥ := by
  have hHD : H ≤ normalizer ((H ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxH, hxC⟩
      exact ⟨H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh), mem_centralizer_conj hHL hh hxC⟩
    · rintro ⟨hxH, hxC⟩
      have h1 : h⁻¹ * (h * x * h⁻¹) * h ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem hh) hxH) hh
      have h2 := mem_centralizer_conj hHL (H.inv_mem hh) hxC
      refine ⟨?_, ?_⟩
      · simpa [mul_assoc] using h1
      · simpa [mul_assoc] using h2
  have hDL : L ⊓ (H ⊓ centralizer (L : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxL, -, hxC⟩
    have : x = 1 := hZ x hxL (fun l hl => (Subgroup.mem_centralizer_iff.mp hxC l hl).symm)
    rw [this]; exact one_mem _
  refine ⟨hHD, ?_, hDL⟩
  set D : Subgroup G := H ⊓ centralizer (L : Set G) with hD
  have hDH : D ≤ H := inf_le_left
  have hDnorm : D ≤ normalizer (L : Set G) := hDH.trans hHL
  have h1 := card_sup_mul_card_inf_of_le_normalizer' hDnorm
  rw [inf_comm, hDL, Subgroup.card_bot, mul_one, hL12] at h1
  have h2 : Nat.card (D ⊔ L : Subgroup G) ∣ Nat.card H := Subgroup.card_dvd_of_le (sup_le hDH hLH)
  rw [h1, hcardH] at h2
  have h3 : Nat.card D ∣ Nat.card S := by
    have h4 : 4 * Nat.card D ∣ Nat.card S := by
      have : 3 * (4 * Nat.card D) ∣ 3 * Nat.card S := by
        have e : Nat.card D * 12 = 3 * (4 * Nat.card D) := by ring
        rw [← e]; exact h2
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    exact (Dvd.intro_left 4 rfl).trans h4
  obtain ⟨a, ha⟩ := hS2.exists_card_eq
  rw [ha] at h3
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  have hD2 : IsPGroup 2 D := IsPGroup.of_card hk
  exact hSyl D hDH hHD hD2

theorem exists_u0_centralizer [Finite G] {H L U : Subgroup G} {c : G}
    (hHL : H ≤ normalizer (L : Set G)) (hUL : U ≤ L) (hcL : c ∈ L)
    (hLeq : L = U ⊔ zpowers c) (hL12 : Nat.card L = 12) (hU4 : Nat.card U = 4)
    (hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hcU : c ∈ normalizer (U : Set G))
    (hfpf : ∀ u ∈ U, u ≠ 1 → c * u * c⁻¹ ≠ u) {h : G} (hh : h ∈ H)
    (hhU : ∀ u ∈ U, h * u = u * h) :
    ∃ u₀ ∈ U, u₀⁻¹ * h ∈ centralizer (L : Set G) := by
  classical
  have hcU' : ∀ u ∈ U, c * u * c⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hcU u).mp hu
  have hcinvU : ∀ u ∈ U, c⁻¹ * u * c ∈ U := by
    intro u hu
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hcU) u).mp hu
    simpa using this
  have hhU' : ∀ u ∈ U, h⁻¹ * u * h = u := by
    intro u hu
    have := hhU u hu
    calc h⁻¹ * u * h = h⁻¹ * (u * h) := by group
      _ = h⁻¹ * (h * u) := by rw [this]
      _ = u := by group
  set c' : G := h * c * h⁻¹ with hc'
  have hc'L : c' ∈ L := (Subgroup.mem_normalizer_iff.mp (hHL hh) c).mp hcL
  set w : G := c⁻¹ * c' with hw
  have hwL : w ∈ L := L.mul_mem (L.inv_mem hcL) hc'L
  have hc'act : ∀ u ∈ U, c' * u * c'⁻¹ = c * u * c⁻¹ := by
    intro u hu
    have hv : c * u * c⁻¹ ∈ U := hcU' u hu
    have h1 := hhU _ hv
    have h2 := hhU' u hu
    calc c' * u * c'⁻¹ = h * c * (h⁻¹ * u * h) * c⁻¹ * h⁻¹ := by simp only [hc']; group
      _ = h * (c * u * c⁻¹) * h⁻¹ := by rw [h2]; group
      _ = c * u * c⁻¹ := by rw [h1]; group
  have hwU : ∀ u ∈ U, w * u * w⁻¹ = u := by
    intro u hu
    calc w * u * w⁻¹ = c⁻¹ * (c' * u * c'⁻¹) * c := by simp only [hw]; group
      _ = c⁻¹ * (c * u * c⁻¹) * c := by rw [hc'act u hu]
      _ = u := by group
  have hwmemU : w ∈ U := by
    set C : Subgroup G := L ⊓ centralizer (U : Set G) with hC
    have hUC : U ≤ C := fun u hu => ⟨hUL hu, Subgroup.mem_centralizer_iff.mpr
      (fun v hv => hUc v hv u hu)⟩
    have hCL : C ≤ L := inf_le_left
    have hd4 : 4 ∣ Nat.card C := hU4 ▸ Subgroup.card_dvd_of_le hUC
    have hd12 : Nat.card C ∣ 12 := hL12 ▸ Subgroup.card_dvd_of_le hCL
    have hCcard : Nat.card C = 4 := by
      by_contra hne
      have h12 : Nat.card C = 12 := by
        have hle : Nat.card C ≤ 12 := Nat.le_of_dvd (by norm_num) hd12
        obtain ⟨m, hm⟩ := hd4
        have hm3 : m ≤ 3 := by omega
        interval_cases m <;> simp_all
      have hCL' : C = L := Subgroup.eq_of_le_of_card_ge hCL (by omega)
      have hcC : c ∈ C := hCL' ▸ hcL
      obtain ⟨u, hu, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
        by_contra hcon
        have hsub : ∀ u ∈ U, u = 1 := by
          intro u hu; by_contra h1; exact hcon ⟨u, hu, h1⟩
        have : Nat.card U = 1 := by
          rw [Nat.card_eq_one_iff_unique]
          exact ⟨⟨fun a b => Subtype.ext (by rw [hsub a a.2, hsub b b.2])⟩, ⟨1⟩⟩
        omega
      apply hfpf u hu hu1
      have := Subgroup.mem_centralizer_iff.mp hcC.2 u hu
      calc c * u * c⁻¹ = (u * c) * c⁻¹ := by rw [this]
        _ = u := by group
    have hCU : C = U := (Subgroup.eq_of_le_of_card_ge hUC (by omega)).symm
    have hwC : w ∈ C := ⟨hwL, Subgroup.mem_centralizer_iff.mpr (fun u hu => by
      have := hwU u hu
      calc u * w = (w * u * w⁻¹) * w := by rw [this]
        _ = w * u := by group)⟩
    exact hCU ▸ hwC
  let θ : U → U := fun u => ⟨c⁻¹ * (u : G) * c * (u : G)⁻¹,
    U.mul_mem (hcinvU u u.2) (U.inv_mem u.2)⟩
  have hθinj : Function.Injective θ := by
    intro a b hab
    have hab' : c⁻¹ * (a : G) * c * (a : G)⁻¹ = c⁻¹ * (b : G) * c * (b : G)⁻¹ :=
      congrArg Subtype.val hab
    set t : G := (a : G) * (b : G)⁻¹ with ht
    have htU : t ∈ U := U.mul_mem a.2 (U.inv_mem b.2)
    have hθa : c⁻¹ * (a : G) * c * (a : G)⁻¹ ∈ U := U.mul_mem (hcinvU a a.2) (U.inv_mem a.2)
    have hcomm := hUc _ hθa t htU
    have h1 : c⁻¹ * t * c = t := by
      have e1 : c⁻¹ * t * c =
          (c⁻¹ * (a : G) * c * (a : G)⁻¹) * ((a : G) * (b : G)⁻¹) *
            (c⁻¹ * (b : G) * c * (b : G)⁻¹)⁻¹ := by simp only [ht]; group
      rw [e1, ← hab']
      calc (c⁻¹ * (a : G) * c * (a : G)⁻¹) * ((a : G) * (b : G)⁻¹) *
            (c⁻¹ * (a : G) * c * (a : G)⁻¹)⁻¹
          = t * (c⁻¹ * (a : G) * c * (a : G)⁻¹) * (c⁻¹ * (a : G) * c * (a : G)⁻¹)⁻¹ := by
            rw [hcomm]
        _ = t := by group
    have h2 : c * t * c⁻¹ = t := by
      calc c * t * c⁻¹ = c * (c⁻¹ * t * c) * c⁻¹ := by rw [h1]
        _ = t := by group
    have ht1 : t = 1 := by
      by_contra hne
      exact hfpf t htU hne h2
    exact Subtype.ext (mul_inv_eq_one.mp ht1)
  have hθsurj : Function.Surjective θ := Finite.injective_iff_surjective.mp hθinj
  obtain ⟨u₀, hu₀⟩ := hθsurj ⟨w, hwmemU⟩
  have hu₀' : c⁻¹ * (u₀ : G) * c * (u₀ : G)⁻¹ = w := congrArg Subtype.val hu₀
  refine ⟨u₀, u₀.2, ?_⟩
  have hc'eq : c' = (u₀ : G) * c * (u₀ : G)⁻¹ := by
    calc c' = c * w := by simp only [hw]; group
      _ = c * (c⁻¹ * (u₀ : G) * c * (u₀ : G)⁻¹) := by rw [hu₀']
      _ = (u₀ : G) * c * (u₀ : G)⁻¹ := by group
  have hvc : (u₀ : G)⁻¹ * h * c = c * ((u₀ : G)⁻¹ * h) := by
    have : h * c * h⁻¹ = (u₀ : G) * c * (u₀ : G)⁻¹ := hc'eq
    calc (u₀ : G)⁻¹ * h * c = (u₀ : G)⁻¹ * (h * c * h⁻¹) * h := by group
      _ = (u₀ : G)⁻¹ * ((u₀ : G) * c * (u₀ : G)⁻¹) * h := by rw [this]
      _ = c * ((u₀ : G)⁻¹ * h) := by group
  have hvU : ∀ u ∈ U, (u₀ : G)⁻¹ * h * u = u * ((u₀ : G)⁻¹ * h) := by
    intro u hu
    calc (u₀ : G)⁻¹ * h * u = (u₀ : G)⁻¹ * (h * u) := by group
      _ = (u₀ : G)⁻¹ * (u * h) := by rw [hhU u hu]
      _ = (u₀ : G)⁻¹ * u * h := by group
      _ = (u * (u₀ : G)⁻¹) * h := by rw [hUc _ (U.inv_mem u₀.2) u hu]
      _ = u * ((u₀ : G)⁻¹ * h) := by group
  have hLle : L ≤ centralizer ({(u₀ : G)⁻¹ * h} : Set G) := by
    rw [hLeq]
    refine sup_le ?_ ?_
    · intro u hu
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hvU u hu).symm
    · rw [zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hvc.symm
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp (hLle hl)

theorem card_S_dich [Finite G] {S U : Subgroup G} (hSU : S ≤ normalizer (U : Set G))
    (hU4 : Nat.card U = 4) (hS2 : IsPGroup 2 S) :
    Nat.card S = Nat.card (S ⊓ centralizer (U : Set G) : Subgroup G) ∨
      Nat.card S = 2 * Nat.card (S ⊓ centralizer (U : Set G) : Subgroup G) := by
  classical
  have hconj : ∀ s : S, ∀ u : U, (s : G) * u * (s : G)⁻¹ ∈ U := fun s u =>
    (Subgroup.mem_normalizer_iff.mp (hSU s.2) u).mp u.2
  have hconj' : ∀ s : S, ∀ u : U, (s : G)⁻¹ * u * (s : G) ∈ U := fun s u => by
    have := (Subgroup.mem_normalizer_iff.mp (hSU (S.inv_mem s.2)) u).mp u.2
    simpa using this
  let cu : S → U → U := fun s u => ⟨(s : G) * u * (s : G)⁻¹, hconj s u⟩
  let cu' : S → U → U := fun s u => ⟨(s : G)⁻¹ * u * (s : G), hconj' s u⟩
  have hcu1 : ∀ s u, cu' s (cu s u) = u := fun s u => Subtype.ext (by
    show (s : G)⁻¹ * ((s : G) * u * (s : G)⁻¹) * (s : G) = u
    group)
  have hcu2 : ∀ s u, cu s (cu' s u) = u := fun s u => Subtype.ext (by
    show (s : G) * ((s : G)⁻¹ * u * (s : G)) * (s : G)⁻¹ = u
    group)
  have hne : ∀ s u, u ≠ 1 → cu s u ≠ 1 := by
    intro s u hu h
    apply hu
    have := congrArg (cu' s) h
    rw [hcu1] at this
    rw [this]
    exact Subtype.ext (by
      show (s : G)⁻¹ * 1 * (s : G) = 1
      group)
  have hne' : ∀ s u, u ≠ 1 → cu' s u ≠ 1 := by
    intro s u hu h
    apply hu
    have := congrArg (cu s) h
    rw [hcu2] at this
    rw [this]
    exact Subtype.ext (by
      show (s : G) * 1 * (s : G)⁻¹ = 1
      group)
  let ρ : S →* Equiv.Perm {u : U // u ≠ 1} :=
    { toFun := fun s =>
        { toFun := fun ω => ⟨cu s ω.1, hne s ω.1 ω.2⟩
          invFun := fun ω => ⟨cu' s ω.1, hne' s ω.1 ω.2⟩
          left_inv := fun ω => Subtype.ext (hcu1 s ω.1)
          right_inv := fun ω => Subtype.ext (hcu2 s ω.1) }
      map_one' := by
        ext ω
        show (1 : G) * ω.1 * (1 : G)⁻¹ = ω.1
        group
      map_mul' := by
        intro s t
        ext ω
        show ((s * t : S) : G) * ω.1 * ((s * t : S) : G)⁻¹ =
          (s : G) * ((t : G) * ω.1 * (t : G)⁻¹) * (s : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group }
  have hker : ρ.ker = (S ⊓ centralizer (U : Set G)).subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine ⟨s.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro u hu
      by_cases hu1 : (⟨u, hu⟩ : U) = 1
      · have : u = 1 := congrArg Subtype.val hu1
        rw [this]; simp
      · have := congrArg (fun σ : Equiv.Perm {u : U // u ≠ 1} => (σ ⟨⟨u, hu⟩, hu1⟩).1.1) h
        simp only [ρ, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, Equiv.Perm.coe_one,
          id_eq] at this
        change (s : G) * u * (s : G)⁻¹ = u at this
        calc u * (s : G) = ((s : G) * u * (s : G)⁻¹) * (s : G) := by rw [this]
          _ = (s : G) * u := by group
    · rintro ⟨-, hs⟩
      ext ω
      show (s : G) * ω.1 * (s : G)⁻¹ = ω.1
      have := Subgroup.mem_centralizer_iff.mp hs ω.1 ω.1.2
      calc (s : G) * ω.1 * (s : G)⁻¹ = (ω.1 * (s : G)) * (s : G)⁻¹ := by rw [this]
        _ = ω.1 := by group
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  have hcardΩ : Nat.card {u : U // u ≠ 1} = 3 := by
    have := Fintype.ofFinite U
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [Nat.card_eq_fintype_card] at hU4
    simp [hU4]
  have h2 : Nat.card (S ⧸ ρ.ker) ∣ 6 := by
    have := Subgroup.card_dvd_of_injective (QuotientGroup.kerLift ρ)
      (QuotientGroup.kerLift_injective ρ)
    rwa [Nat.card_perm, hcardΩ] at this
  have h3 : Nat.card (S ⧸ ρ.ker) ∣ Nat.card S := Dvd.intro _ h1.symm
  obtain ⟨a, ha⟩ := hS2.exists_card_eq
  rw [ha] at h3
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  have hjle : j ≤ 1 := by
    by_contra hcon
    have hcon := not_le.mp hcon
    have h4 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 hcon
    rw [← hj] at h4
    have := h4.trans h2
    omega
  have hker' : Nat.card ρ.ker = Nat.card (S ⊓ centralizer (U : Set G) : Subgroup G) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hker'] at h1
  interval_cases j
  · left; rw [pow_zero] at hj; rw [h1, hj]; ring
  · right; rw [pow_one] at hj; rw [h1, hj]

theorem a3_generic [Finite G] {H S L U : Subgroup G} {c : G}
    (hH : H = L ⊔ S) (hSH : S ≤ H) (hSL : S ≤ normalizer (L : Set G)) (hS2 : IsPGroup 2 S)
    (hSyl : ∀ N : Subgroup G, N ≤ H → H ≤ normalizer (N : Set G) → IsPGroup 2 N → N ≤ S)
    (hHU : H ≤ normalizer (U : Set G)) (hUL : U ≤ L) (hU4 : Nat.card U = 4)
    (hUe : ∀ u ∈ U, u ^ 2 = 1) (hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    (hcL : c ∈ L) (hcU : c ∈ normalizer (U : Set G)) (hfpf : ∀ u ∈ U, u ≠ 1 → c * u * c⁻¹ ≠ u)
    (hLeq : L = U ⊔ zpowers c) (hL12 : Nat.card L = 12)
    (hZ : ∀ g ∈ L, (∀ l ∈ L, g * l = l * g) → g = 1) (hnotnormal : ¬ H ≤ normalizer (S : Set G)) :
    U ≤ S ∧ Nat.card H = 3 * Nat.card S ∧
      H ≤ normalizer ((H ⊓ centralizer (L : Set G) : Subgroup G) : Set G) ∧
      H ⊓ centralizer (L : Set G) ≤ S ∧ U ⊓ (H ⊓ centralizer (L : Set G)) = ⊥ ∧
      S ⊓ centralizer (U : Set G) = U ⊔ (H ⊓ centralizer (L : Set G)) ∧
      Nat.card S = 8 * Nat.card (H ⊓ centralizer (L : Set G) : Subgroup G) := by
  classical
  have hLH : L ≤ H := hH ▸ le_sup_left
  have hHL : H ≤ normalizer (L : Set G) :=
    hH ▸ sup_le Subgroup.le_normalizer hSL
  have hU2 : IsPGroup 2 U := fun g => ⟨1, by simpa using Subtype.ext (hUe g g.2)⟩
  have hUS : U ≤ S := hSyl U (hUL.trans hLH) hHU hU2
  have hcardH := card_H_eq hH hSL hS2 hL12 hU4 hUL hUS
  obtain ⟨hHD, hDS, hDL⟩ := D_facts hHL hLH hcardH hS2 hL12 hZ hSyl
  set D : Subgroup G := H ⊓ centralizer (L : Set G) with hD
  have hUD : U ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ L ⊓ D := ⟨hUL hx.1, hx.2⟩
    rw [hDL] at this
    exact this
  have hSC : S ⊓ centralizer (U : Set G) = U ⊔ D := by
    apply le_antisymm
    · rintro s ⟨hsS, hsC⟩
      obtain ⟨u₀, hu₀, hv⟩ := exists_u0_centralizer hHL hUL hcL hLeq hL12 hU4 hUc hcU hfpf
        (hSH hsS) (fun u hu => (Subgroup.mem_centralizer_iff.mp hsC u hu).symm)
      have hvD : u₀⁻¹ * s ∈ D := ⟨H.mul_mem (H.inv_mem (hUL.trans hLH hu₀)) (hSH hsS), hv⟩
      have : s = u₀ * (u₀⁻¹ * s) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hu₀) (Subgroup.mem_sup_right hvD)
    · refine sup_le ?_ ?_
      · intro u hu
        exact ⟨hUS hu, Subgroup.mem_centralizer_iff.mpr (fun v hv => hUc v hv u hu)⟩
      · intro d hd
        exact ⟨hDS hd, Subgroup.mem_centralizer_iff.mpr
          (fun v hv => Subgroup.mem_centralizer_iff.mp hd.2 v (hUL hv))⟩
  have hcardK : Nat.card (U ⊔ D : Subgroup G) = 4 * Nat.card D := by
    have hUN : U ≤ normalizer (D : Set G) := (hUL.trans hLH).trans hHD
    have := card_sup_mul_card_inf_of_le_normalizer' hUN
    rw [hUD, Subgroup.card_bot, mul_one, hU4] at this
    exact this
  have hSU : S ≤ normalizer (U : Set G) := hSH.trans hHU
  have hdich := card_S_dich hSU hU4 hS2
  rw [hSC, hcardK] at hdich
  refine ⟨hUS, hcardH, hHD, hDS, hUD, hSC, ?_⟩
  rcases hdich with h | h
  · exfalso
    have hle : U ⊔ D ≤ S := hSC ▸ inf_le_left
    have hSeq : U ⊔ D = S := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardK]; omega)
    apply hnotnormal
    rw [← hSeq]
    intro h hh
    exact mem_normalizer_sup (hHU hh) (hHD hh)
  · omega

end A3Gen

variable {G : Type} [Group G] [Finite G]

structure A3Local (H S L U D : Subgroup G) (c : G) : Prop where
  card_U : Nat.card U = 4
  U_exp : ∀ u ∈ U, u ^ 2 = 1
  U_comm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u
  c_mem : c ∈ L
  c_order : orderOf c = 3
  c_normalizes : c ∈ Subgroup.normalizer (U : Set G)
  c_fpf : ∀ u ∈ U, u ≠ 1 → c * u * c⁻¹ ≠ u
  L_eq : L = U ⊔ Subgroup.zpowers c
  H_normalizes_L : H ≤ Subgroup.normalizer (L : Set G)
  H_normalizes_U : H ≤ Subgroup.normalizer (U : Set G)
  U_le_S : U ≤ S
  card_H : Nat.card H = 3 * Nat.card S
  D_eq : D = H ⊓ Subgroup.centralizer (L : Set G)
  D_le_S : D ≤ S
  H_normalizes_D : H ≤ Subgroup.normalizer (D : Set G)
  D_comm_L : ∀ d ∈ D, ∀ l ∈ L, d * l = l * d
  U_inf_D : U ⊓ D = ⊥
  S_cent_U : S ⊓ Subgroup.centralizer (U : Set G) = U ⊔ D
  card_S : Nat.card S = 8 * Nat.card D

theorem ConstrainedSetting.a3Local {T M H S L : Subgroup G}
    (hcs : ConstrainedSetting G T M H S L) (h3 : IsAltType L 3) (hj : conjJoin S L = L) :
    ∃ (U D : Subgroup G) (c : G), A3Local H S L U D c := by
  classical
  obtain ⟨hQU, hcardU, hUexp, hUcomm, hcardL, hZL, c, hcL, hc3, hcnorm, hfpf, hLeq⟩ :=
    hcs.block.1.1.alt3_structure h3
  have hH : H = L ⊔ S := by rw [hcs.eq_join, hj]
  have hSH : S ≤ H := hcs.sylow.1
  have hSL : S ≤ normalizer (L : Set G) := by
    have h1 : ∀ t ∈ S, L.map (MulAut.conj t).toMonoidHom ≤ L := by
      intro t ht
      have h : L.map (MulAut.conj t).toMonoidHom ≤ conjJoin S L :=
        le_iSup (fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨t, ht⟩
      rwa [hj] at h
    intro s hs
    apply A3Gen.mem_normalizer_of_map_conj_eq
    refine le_antisymm (h1 s hs) ?_
    intro x hx
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have h2 : (MulAut.conj s⁻¹) x ∈ L.map (MulAut.conj s⁻¹).toMonoidHom := ⟨x, hx, rfl⟩
    have h3 := h1 s⁻¹ (S.inv_mem hs) h2
    simpa [MulAut.conj_apply] using h3
  have hHL : H ≤ normalizer (L : Set G) := hH ▸ sup_le Subgroup.le_normalizer hSL
  have hHU : H ≤ normalizer (blockU L : Set G) := by
    intro h hh
    apply A3Gen.mem_normalizer_of_map_conj_eq
    rw [← hQU]
    unfold blockQ
    rw [← pCoreOf_map_equiv 2 (MulAut.conj h) L, A3Gen.map_conj_eq_of_mem_normalizer (hHL hh)]
  have hUL : blockU L ≤ L := hQU ▸ CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L
  obtain ⟨hUS, hcardH, hHD, hDS, hUD, hSC, hcardS⟩ :=
    A3Gen.a3_generic hH hSH hSL hcs.sylow.2.1
      (fun N hNH hHN hN2 => hcs.sylow.le_of_normalizes hNH hHN hN2) hHU hUL hcardU hUexp hUcomm
      hcL hcnorm hfpf hLeq hcardL hZL hcs.minParabolic.2.1
  exact ⟨blockU L, H ⊓ Subgroup.centralizer (L : Set G), c,
    ⟨hcardU, hUexp, hUcomm, hcL, hc3, hcnorm, hfpf, hLeq, hHL, hHU, hUS, hcardH, rfl, hDS, hHD,
      fun d hd l hl => (Subgroup.mem_centralizer_iff.mp hd.2 l hl).symm, hUD, hSC, hcardS⟩⟩

end CFSG.QuasithinUnique
