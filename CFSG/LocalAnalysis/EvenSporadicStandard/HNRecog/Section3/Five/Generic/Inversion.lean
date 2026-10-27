module

public import Mathlib.GroupTheory.Sylow

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type*} [Group G]

private theorem MulAut.eq_inv_of_fixed_eq_one {A : Type*} [Group A] [Finite A]
    (φ : MulAut A) (hφ : φ * φ = 1) (P : Subgroup A)
    (hP : ∀ x : A, x ∈ P ↔ φ x ∈ P) (hfix : ∀ x ∈ P, φ x = x → x = 1) :
    ∀ x ∈ P, φ x = x⁻¹ := by
  have hφφ : ∀ x, φ (φ x) = x := fun x => by
    have := congrArg (fun β : MulAut A => β x) hφ
    simpa using this
  have hmem : ∀ x : P, (x : A)⁻¹ * φ (x : A) ∈ P := fun x =>
    P.mul_mem (P.inv_mem x.property) ((hP _).mp x.property)
  let f : P → P := fun x => ⟨(x : A)⁻¹ * φ (x : A), hmem x⟩
  have hinj : Function.Injective f := by
    intro x y h
    have h' : (x : A)⁻¹ * φ (x : A) = (y : A)⁻¹ * φ (y : A) := congrArg Subtype.val h
    have h2 : (y : A) * (x : A)⁻¹ = φ (y : A) * (φ (x : A))⁻¹ := by
      calc (y : A) * (x : A)⁻¹
          = (y : A) * (x : A)⁻¹ * φ (x : A) * (φ (x : A))⁻¹ := by group
        _ = (y : A) * ((x : A)⁻¹ * φ (x : A)) * (φ (x : A))⁻¹ := by group
        _ = (y : A) * ((y : A)⁻¹ * φ (y : A)) * (φ (x : A))⁻¹ := by rw [h']
        _ = φ (y : A) * (φ (x : A))⁻¹ := by group
    have h3 : φ ((y : A) * (x : A)⁻¹) = (y : A) * (x : A)⁻¹ := by
      rw [map_mul, map_inv, ← h2]
    have hmem' : (y : A) * (x : A)⁻¹ ∈ P := P.mul_mem y.property (P.inv_mem x.property)
    have h4 : (y : A) * (x : A)⁻¹ = 1 := hfix _ hmem' h3
    exact Subtype.ext (mul_inv_eq_one.mp h4).symm
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hy' : (y : A)⁻¹ * φ (y : A) = x := congrArg Subtype.val hy
  calc φ x = φ ((y : A)⁻¹ * φ (y : A)) := by rw [hy']
    _ = (φ (y : A))⁻¹ * φ (φ (y : A)) := by rw [map_mul, map_inv]
    _ = (φ (y : A))⁻¹ * (y : A) := by rw [hφφ]
    _ = ((y : A)⁻¹ * φ (y : A))⁻¹ := by group
    _ = x⁻¹ := by rw [hy']

theorem exists_inverted_element {K N : Subgroup G} [Finite K] (hNK : N ≤ K)
    (hNn : (N.subgroupOf K).Normal) (hodd : ¬ 2 ∣ Nat.card ↥N) {a : G} (haK : a ∈ K)
    (ha : a * a = 1) {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card ↥N)
    (hC : ¬ p ∣ Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set G))) :
    ∃ σ ∈ N, orderOf σ = p ∧ a * σ * a = σ⁻¹ := by
  classical
  let N' : Subgroup K := N.subgroupOf K
  haveI hN'mem : N'.Normal := hNn
  let e : ↥N' ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNK
  have hcardN' : Nat.card ↥N' = Nat.card ↥N := Nat.card_congr e.toEquiv
  have hodd' : ¬ 2 ∣ Nat.card ↥N' := by rwa [hcardN']
  have hp' : p ∣ Nat.card ↥N' := by rwa [hcardN']
  let ak : K := ⟨a, haK⟩
  have hak2 : ak * ak = 1 := Subtype.ext ha
  let T : Subgroup K := Subgroup.zpowers ak
  let t : T := ⟨ak, Subgroup.mem_zpowers ak⟩
  have ht2 : t * t = 1 := Subtype.ext hak2
  have hT2 : IsPGroup 2 T := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    simpa using (orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hak2)))
  letI : MulDistribMulAction T ↥N' :=
    MulDistribMulAction.compHom ↥N' ((MulAut.conjNormal (H := N')).comp T.subtype)
  haveI : Finite (Sylow p ↥N') :=
    Sylow.finite_of_finiteIndex (default : Sylow p ↥N')
  have hcardSyl_dvd : Nat.card (Sylow p ↥N') ∣ Nat.card ↥N' :=
    (Sylow.card_dvd_index (default : Sylow p ↥N')).trans
      (Subgroup.index_dvd_card ((default : Sylow p ↥N') : Subgroup ↥N'))
  have hcardSyl : ¬ 2 ∣ Nat.card (Sylow p ↥N') := fun h => hodd' (h.trans hcardSyl_dvd)
  obtain ⟨P, hPmem⟩ := hT2.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p ↥N') hcardSyl
  have hPfix : ∀ s : T, s • P = P := MulAction.mem_fixedPoints.mp hPmem
  have hPt : t • P = P := hPfix t
  have hPsub : t • (P : Subgroup ↥N') = (P : Subgroup ↥N') := by
    rw [← Sylow.pointwise_smul_def, hPt]
  let C : Subgroup ↥N' :=
    { carrier := {x | x ∈ (P : Subgroup ↥N') ∧ t • x = x}
      mul_mem' := by
        intro x y hx hy
        exact ⟨(P : Subgroup ↥N').mul_mem hx.1 hy.1, by rw [smul_mul', hx.2, hy.2]⟩
      one_mem' := ⟨(P : Subgroup ↥N').one_mem, smul_one t⟩
      inv_mem' := by
        intro x hx
        exact ⟨(P : Subgroup ↥N').inv_mem hx.1, by rw [smul_inv', hx.2]⟩ }
  have hCdiv : Nat.card C ∣ Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) := by
    let f : ↥N' →* G := K.subtype.comp N'.subtype
    have hf : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext hxy)
    have hle : C.map f ≤ K ⊓ Subgroup.centralizer ({a} : Set G) := by
      intro z hz
      obtain ⟨y, hyC, rfl⟩ := Subgroup.mem_map.mp hz
      have hfixy : ak * (y : K) * ak⁻¹ = (y : K) := by
        have h1 : MulAut.conjNormal (H := N') ak y = y := by
          change t • y = y
          exact hyC.2
        have := congrArg (fun x : ↥N' => (x : K)) h1
        simpa [MulAut.conjNormal_apply] using this
      have hakeq : ak⁻¹ = ak := (inv_eq_iff_mul_eq_one).mpr hak2
      have hcomm : a * (f y) = (f y) * a := by
        have h1 : ak * (y : K) * ak = (y : K) := by rwa [hakeq] at hfixy
        have h2 : a * (f y) * a = f y := by
          have := congrArg (fun x : K => (x : G)) h1
          simpa [f, ak] using this
        have h3 := congrArg (fun z => z * a) h2
        simpa [mul_assoc, ha] using h3
      exact ⟨(N'.subtype y).property, Subgroup.mem_centralizer_iff.mpr (by
        intro b hb
        rw [Set.mem_singleton_iff] at hb
        subst hb
        exact hcomm)⟩
    have hcardmap : Nat.card (C.map f) = Nat.card C := Subgroup.card_map_of_injective hf
    rw [← hcardmap]
    exact Subgroup.card_dvd_of_le hle
  have hleCP : C ≤ (P : Subgroup ↥N') := fun x hx => hx.1
  have hCbot : C = ⊥ := by
    rcases (P.isPGroup'.to_le hleCP).card_eq_or_dvd with hone | hpdvd
    · exact C.eq_bot_of_card_eq hone
    · exact absurd (hpdvd.trans hCdiv) hC
  have hφ : MulAut.conjNormal (H := N') ak * MulAut.conjNormal (H := N') ak = 1 := by
    rw [← map_mul (MulAut.conjNormal (H := N')) ak ak, hak2, map_one]
  have hPiff : ∀ x : ↥N', x ∈ (P : Subgroup ↥N') ↔
      MulAut.conjNormal (H := N') ak x ∈ (P : Subgroup ↥N') := by
    intro x
    have hmem : x ∈ t • (P : Subgroup ↥N') ↔ t⁻¹ • x ∈ (P : Subgroup ↥N') :=
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem
    rw [hPsub] at hmem
    rw [show t⁻¹ = t from by rw [inv_eq_iff_mul_eq_one]; exact ht2] at hmem
    exact hmem
  have hfix : ∀ x ∈ (P : Subgroup ↥N'), MulAut.conjNormal (H := N') ak x = x → x = 1 := by
    intro x hx hφx
    have htx : t • x = x := by
      change MulAut.conjNormal (H := N') ak x = x
      exact hφx
    have hxC : x ∈ C := ⟨hx, htx⟩
    have hx1 : x = 1 := by simpa [hCbot] using hxC
    exact hx1
  have hαinv : ∀ x ∈ (P : Subgroup ↥N'), MulAut.conjNormal (H := N') ak x = x⁻¹ :=
    MulAut.eq_inv_of_fixed_eq_one (MulAut.conjNormal (H := N') ak) hφ (P : Subgroup ↥N') hPiff hfix
  have hpdvdP : p ∣ Nat.card ↥(P : Subgroup ↥N') := P.dvd_card_of_dvd_card hp'
  obtain ⟨σP, hσPorder⟩ := exists_prime_orderOf_dvd_card' p hpdvdP
  let g : ↥(P : Subgroup ↥N') →* G :=
    K.subtype.comp (N'.subtype.comp (P : Subgroup ↥N').subtype)
  have hg : Function.Injective g := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (Subtype.ext hxy))
  refine ⟨g σP, ?_, ?_, ?_⟩
  · change ((σP : ↥N') : G) ∈ N
    exact Subgroup.mem_subgroupOf.mp (σP : ↥N').property
  · rw [orderOf_injective g hg σP, hσPorder]
  · have hN'inv : MulAut.conjNormal (H := N') ak (σP : ↥N') = (σP : ↥N')⁻¹ :=
      hαinv (σP : ↥N') σP.property
    have hKinv : ak * ((σP : ↥N') : K) * ak⁻¹ = ((σP : ↥N') : K)⁻¹ := by
      have := congrArg (fun x : ↥N' => (x : K)) hN'inv
      simpa [MulAut.conjNormal_apply] using this
    have hGinv : a * g σP * a⁻¹ = (g σP)⁻¹ := by
      have := congrArg (fun x : K => (x : G)) hKinv
      simpa [g, ak] using this
    have hakeq : a⁻¹ = a := (inv_eq_iff_mul_eq_one).mpr ha
    simpa [hakeq] using hGinv

end CFSG.EvenSporadicStandard.HNRecog.Section3
