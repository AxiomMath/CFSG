module

public import CFSG.CGT.PushingUpLit.C2L.Gomi3
public import CFSG.CGT.PushingUpLit.T2KSW.Irred

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG.ABGLocalTools CFSG.CGT.PushingUpLit.T2KSW
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Gomi41

theorem mem_normalizer_of_forall_conj_mem {Y : Type*} [Group Y] [Finite Y] {B : Subgroup Y}
    {m : Y} (h : ∀ y ∈ B, m * y * m⁻¹ ∈ B) : m ∈ Subgroup.normalizer (B : Set Y) := by
  have hle : B.map (MulAut.conj m).toMonoidHom ≤ B := by
    rintro _ ⟨y, hy, rfl⟩
    simpa using h y hy
  have heq : B.map (MulAut.conj m).toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj m).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq

theorem card_eq_card_map_mul_card_inf_ker {R G : Type*} [Group R] [Group G] (φ : R →* G)
    (H : Subgroup R) : Nat.card H = Nat.card (H.map φ) * Nat.card (H ⊓ φ.ker : Subgroup R) := by
  let ψ : H →* G := φ.comp H.subtype
  have hrange : ψ.range = H.map φ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ψ.ker = Nat.card (H ⊓ φ.ker : Subgroup R) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : H) : R), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker]

theorem bender_quotient {Z : Type} [Group Z] [Finite Z]
    {T Q : Subgroup Z} [Q.Normal] (hT : IsSylowOf 2 T ⊤) (hQT : Q ≤ T) (hlt : Q < T)
    (hTQ : ∀ x ∈ T, ∀ y ∈ T, x ^ 2 ∈ Q ∧ ⁅x, y⁆ ∈ Q)
    (hSE : ∃ K : Subgroup (Z ⧸ Q), CFSG.Open.fusionStronglyEmbedded K) :
    Nat.card T = 2 * Nat.card Q ∨ ∀ P : Subgroup Z, P ≤ T →
      Subgroup.normalizer (T : Set Z) ≤ Subgroup.normalizer (P : Set Z) → P ≤ Q ∨ P ⊔ Q = T := by
  obtain ⟨K, hK⟩ := hSE
  set π : Z →* Z ⧸ Q := QuotientGroup.mk' Q
  have hker : π.ker = Q := QuotientGroup.ker_mk' Q
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hB : IsSylowOf 2 (T.map π) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, hT.isPGroup.map π, ?_⟩
    rw [Subgroup.relIndex_top_right]
    intro h
    have h1 := h.trans (Subgroup.index_map_dvd T hπsurj)
    have hT' := (isSylowOf_iff.1 hT).2.2
    rw [Subgroup.relIndex_top_right] at hT'
    exact hT' h1
  have hBab : ∀ a ∈ T.map π, ∀ b ∈ T.map π, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    have h := (hTQ y⁻¹ (T.inv_mem hy) x⁻¹ (T.inv_mem hx)).2
    rw [commutatorElement_def] at h
    exact QuotientGroup.eq.2 (by simpa [mul_assoc] using h)
  have hBexp : ∀ a ∈ T.map π, a * a = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff (x * x)).2 (by simpa [pow_two] using (hTQ x hx x hx).1)
  have hB1 : T.map π ≠ ⊥ := by
    intro h
    obtain ⟨t, htT, htQ⟩ := IsConcreteLE.exists_of_lt hlt
    have h1 : π t = 1 := by
      have := Subgroup.mem_map_of_mem π htT
      rw [h, Subgroup.mem_bot] at this
      exact this
    exact htQ ((QuotientGroup.eq_one_iff t).1 h1)
  rcases card_eq_two_or_irreducible hK hB hBab hBexp hB1 with h2 | hirr
  · left
    have hcard := card_eq_card_map_mul_card_inf_ker π T
    rw [hker, inf_eq_right.2 hQT, h2] at hcard
    exact hcard
  · right
    intro P hPT hNP
    have hPB : P.map π ≤ T.map π := Subgroup.map_mono hPT
    have hcomapT : (T.map π).comap π = T := by
      rw [Subgroup.comap_map_eq, hker, sup_eq_left.2 hQT]
    have hTmem : ∀ y, y ∈ T ↔ π y ∈ T.map π := fun y => by
      rw [← Subgroup.mem_comap, hcomapT]
    rcases hirr (P.map π) hPB (by
        intro x hx
        obtain ⟨m, rfl⟩ := hπsurj x
        have hmT : m ∈ Subgroup.normalizer (T : Set Z) := by
          rw [Subgroup.mem_normalizer_iff]
          intro y
          rw [hTmem y, hTmem (m * y * m⁻¹), map_mul, map_mul, map_inv]
          exact Subgroup.mem_normalizer_iff.1 hx (π y)
        have hmP := hNP hmT
        apply mem_normalizer_of_forall_conj_mem
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨m * p * m⁻¹, (Subgroup.mem_normalizer_iff.1 hmP p).1 hp, by simp⟩) with h | h
    · left
      have := (Subgroup.map_eq_bot_iff P).1 h
      rwa [hker] at this
    · right
      calc P ⊔ Q = (P.map π).comap π := by rw [Subgroup.comap_map_eq, hker]
        _ = (T.map π).comap π := by rw [h]
        _ = T := hcomapT

section Main

variable [Finite G]

theorem exists_sq_mem_normalizer {P K : Subgroup G} (hP : IsPGroup 2 P) (hKP : K < P) :
    ∃ u ∈ P, u ∈ Subgroup.normalizer (K : Set G) ∧ u ∉ K ∧ u * u ∈ K := by
  obtain ⟨u₀, hu₀, hu₀K⟩ := IsConcreteLE.exists_of_lt (lt_inf_normalizer_of_lt hP hKP)
  have hu₀P : u₀ ∈ P := hu₀.1
  have hu₀N : u₀ ∈ Subgroup.normalizer (K : Set G) := hu₀.2
  have hex : ∃ j : ℕ, u₀ ^ 2 ^ j ∈ K := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.1 hP ⟨u₀, hu₀P⟩
    refine ⟨a, ?_⟩
    have h1 := pow_orderOf_eq_one (⟨u₀, hu₀P⟩ : ↥P)
    rw [ha] at h1
    have h2 : u₀ ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val h1
    rw [h2]
    exact K.one_mem
  classical
  have hj0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact hu₀K (by simpa using this)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨u₀ ^ 2 ^ j, P.pow_mem hu₀P _, (Subgroup.normalizer _).pow_mem hu₀N _, ?_, ?_⟩
  · exact Nat.find_min hex (hj ▸ Nat.lt_succ_self j)
  · have := Nat.find_spec hex
    rw [hj, pow_succ, pow_mul] at this
    simpa [pow_two] using this

theorem exists_gomiE_of_not_normal {P D₁ : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (hD₁ : GomiD P D₁) (hnorm : ¬ P ≤ Subgroup.normalizer (D₁ : Set G)) :
    ∃ D₂ : Subgroup G, GomiE P D₁ D₂ := by
  set K : Subgroup G := P ⊓ Subgroup.normalizer (D₁ : Set G) with hK
  have hKP : K < P := lt_of_le_of_ne inf_le_left fun h => hnorm (h ▸ inf_le_right)
  obtain ⟨u, huP, huN, huK, hu2⟩ := exists_sq_mem_normalizer hP.isPGroup hKP
  have hPc : P.map (MulAut.conj u).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer huP)
  have hKc : K.map (MulAut.conj u).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 huN
  have hD₂ : GomiD P (D₁.map (MulAut.conj u).toMonoidHom) := by
    have := hD₁.map_conj u
    rwa [hPc] at this
  refine ⟨D₁.map (MulAut.conj u).toMonoidHom, hD₁, hD₂, ?_, ?_, Or.inr ⟨u, huP, rfl, ?_⟩⟩
  · intro h
    apply huK
    have hu : u ∈ Subgroup.normalizer (D₁ : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 h.symm
    exact ⟨huP, hu⟩
  · have hN : (Subgroup.normalizer (D₁ : Set G)).map (MulAut.conj u).toMonoidHom =
        Subgroup.normalizer ((D₁.map (MulAut.conj u).toMonoidHom : Subgroup G) : Set G) :=
      Subgroup.map_equiv_normalizer_eq D₁ (MulAut.conj u)
    calc P ⊓ Subgroup.normalizer (D₁ : Set G) = K := rfl
      _ = K.map (MulAut.conj u).toMonoidHom := hKc.symm
      _ = P.map (MulAut.conj u).toMonoidHom ⊓
          (Subgroup.normalizer (D₁ : Set G)).map (MulAut.conj u).toMonoidHom :=
        Subgroup.map_inf _ _ _ (MulAut.conj u).injective
      _ = P ⊓ Subgroup.normalizer ((D₁.map (MulAut.conj u).toMonoidHom : Subgroup G) : Set G) := by
        rw [hPc, hN]
  · rw [Subgroup.map_map]
    have hcc : (MulAut.conj u).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
        (MulAut.conj (u * u)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcc]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1 hu2.2

theorem exists_gomiE_of_normal
    (hO : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    (hc : CFSG.Assembly.IsCharTwoType G)
    (hi : ∀ H : Subgroup G, GomiH H → ∀ S : Subgroup G,
      IsSylowOf 2 S (Subgroup.normalizer (H : Set G)) → ClassLETwo S)
    (hZ : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ClassLETwo S →
      ∀ z ∈ S, (∀ y ∈ S, y * z = z * y) → z * z = 1)
    {P D₁ : Subgroup G} (hP : IsSylowOf 2 P ⊤) (hD₁ : GomiD P D₁)
    (hnorm : P ≤ Subgroup.normalizer (D₁ : Set G)) :
    ∃ D₂ : Subgroup G, GomiE P D₁ D₂ := by
  have hclass : ClassLETwo P := hi D₁ hD₁.1.1 P (hP.of_le hnorm le_top)
  have hPnormal : ∀ H : Subgroup G, GomiH H → H ≤ P → P ≤ Subgroup.normalizer (H : Set G) :=
    fun H hH hHP => hH.le_normalizer_of_classLETwo hc hclass hHP
  by_cases hex : ∃ D₂ : Subgroup G, GomiD P D₂ ∧ D₂ ≠ D₁
  · obtain ⟨D₂, hD₂, hne⟩ := hex
    refine ⟨D₂, hD₁, hD₂, hne.symm, ?_, Or.inl ⟨hnorm, hPnormal D₂ hD₂.1.1 hD₂.1.2⟩⟩
    rw [inf_eq_left.2 hnorm, inf_eq_left.2 (hPnormal D₂ hD₂.1.1 hD₂.1.2)]
  exfalso
  push Not at hex
  obtain ⟨H, hH, hHne⟩ : ∃ H : Subgroup G, GomiH0In P H ∧ H ≠ D₁ := by
    rcases gomiH0In_empty_or_two hO hO2 hP with h | ⟨H₁, H₂, hne, h₁, h₂⟩
    · exact absurd ⟨hD₁.gomiH0 hP, hD₁.1.2⟩ (h D₁)
    · by_cases h1 : H₁ = D₁
      · exact ⟨H₂, h₂, fun h => hne (h1.trans h.symm)⟩
      · exact ⟨H₁, h₁, h1⟩
  have hHP : H ≤ P := hH.2
  have hHg : GomiH H := hH.1.1
  obtain ⟨M, hHM, hM⟩ := exists_maximal_ge_of_wellFoundedGT (GomiHIn P) H ⟨hHg, hHP⟩
  have hHD : H < D₁ := lt_of_le_of_ne ((hex M hM) ▸ hHM) hHne
  have hDP : D₁ < P := hD₁.lt hP
  have hHltP : H < P := lt_of_lt_of_le hHD hDP.le
  have hcenter : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → z ∈ H := fun z hz hzc =>
    hHg.center_le hc hHP ⟨hz, Subgroup.mem_centralizer_iff.2 hzc⟩
  have hZ' := hZ P hP hclass
  have hcommP : ∀ x ∈ P, ∀ w ∈ P, ⁅x, w⁆ ∈ P := fun x hx w hw => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hx hw) (P.inv_mem hx)) (P.inv_mem hw)
  have hcentral : ∀ x ∈ P, ∀ w ∈ P, ∀ y ∈ P, y * ⁅x, w⁆ = ⁅x, w⁆ * y := fun x hx w hw y hy =>
    (commutatorElement_eq_one_iff_mul_comm.1 (hclass x hx w hw y hy)).symm
  have hcomm : ∀ x ∈ P, ∀ w ∈ P, ⁅x, w⁆ ∈ H := fun x hx w hw =>
    hcenter _ (hcommP x hx w hw) (hcentral x hx w hw)
  have hsq : ∀ x ∈ P, x ^ 2 ∈ H := by
    intro x hx
    rw [pow_two]
    refine hcenter _ (P.mul_mem hx hx) fun w hw => ?_
    obtain ⟨c, hc'⟩ : ∃ c : G, c = ⁅x, w⁆ := ⟨_, rfl⟩
    have hcc : c * c = 1 := hc' ▸ hZ' _ (hcommP x hx w hw) (hcentral x hx w hw)
    have hxc : x * c = c * x := hc' ▸ hcentral x hx w hw x hx
    have hxw : x * w = c * w * x := by
      rw [hc', commutatorElement_def]
      group
    calc w * (x * x) = (w * x) * x := (mul_assoc _ _ _).symm
      _ = (c * c * w * x) * x := by rw [hcc, one_mul]
      _ = c * (c * w * x) * x := by group
      _ = c * (x * w) * x := by rw [hxw]
      _ = (c * x) * w * x := by group
      _ = (x * c) * w * x := by rw [hxc]
      _ = x * (c * w * x) := by group
      _ = x * (x * w) := by rw [← hxw]
      _ = (x * x) * w := by group
  have hHq : ∀ x ∈ P, ∀ y ∈ P, x ^ 2 ∈ H ∧ ⁅x, y⁆ ∈ H :=
    fun x hx y hy => ⟨hsq x hx, hcomm x hx y hy⟩
  set N : Subgroup G := Subgroup.normalizer (H : Set G) with hN
  have hHN : H ≤ N := Subgroup.le_normalizer
  have hPN : P ≤ N := hPnormal H hHg hHP
  have hDN : D₁ ≤ N := hD₁.1.2.trans hPN
  have hsyl : IsSylowOf 2 (P.subgroupOf N) ⊤ := by
    rw [isSylowOf_iff]
    obtain ⟨-, hPp, hPi⟩ := isSylowOf_iff.1 hP
    rw [Subgroup.relIndex_top_right] at hPi
    refine ⟨le_top, hPp.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    intro h
    exact hPi (h.trans (Subgroup.relIndex_dvd_index_of_le hPN))
  have hlt' : H.subgroupOf N < P.subgroupOf N := by
    refine lt_of_le_of_ne (fun x hx => hHP hx) fun h => ?_
    obtain ⟨t, htP, htH⟩ := IsConcreteLE.exists_of_lt hHltP
    have ht : (⟨t, hPN htP⟩ : N) ∈ P.subgroupOf N := htP
    rw [← h] at ht
    exact htH ht
  have hTQ' : ∀ x ∈ P.subgroupOf N, ∀ y ∈ P.subgroupOf N,
      x ^ 2 ∈ H.subgroupOf N ∧ ⁅x, y⁆ ∈ H.subgroupOf N := by
    intro x hx y hy
    have h := hHq (x : G) hx (y : G) hy
    refine ⟨Subgroup.mem_subgroupOf.2 ?_, Subgroup.mem_subgroupOf.2 ?_⟩
    · simpa using h.1
    · simpa [commutatorElement_def] using h.2
  rcases bender_quotient (Z := ↥N) (T := P.subgroupOf N) (Q := H.subgroupOf N) hsyl
      (fun x hx => hHP hx) hlt' hTQ' hH.1.2 with hcard | hirr
  ·
    have e1 : Nat.card ↥(P.subgroupOf N) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
    have e2 : Nat.card ↥(H.subgroupOf N) = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv
    rw [e1, e2] at hcard
    have hHpos : 0 < Nat.card H := Nat.card_pos
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHD.le
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hDP.le
    have h1 : Nat.card H * (m * k) = Nat.card H * 2 := by
      calc Nat.card H * (m * k) = Nat.card D₁ * k := by rw [hm]; ring
        _ = Nat.card P := hk.symm
        _ = 2 * Nat.card H := hcard
        _ = Nat.card H * 2 := by ring
    have hmk : m * k = 2 := Nat.eq_of_mul_eq_mul_left hHpos h1
    rcases (Nat.dvd_prime Nat.prime_two).1 (⟨k, hmk.symm⟩ : m ∣ 2) with hm1 | hm2
    · subst hm1
      exact hHne (Subgroup.eq_of_le_of_card_ge hHD.le (by omega))
    · subst hm2
      have hk1 : k = 1 := by omega
      subst hk1
      exact hDP.ne (Subgroup.eq_of_le_of_card_ge hDP.le (by omega))
  ·
    have hNT : Subgroup.normalizer ((P.subgroupOf N : Subgroup ↥N) : Set ↥N) ≤
        Subgroup.normalizer ((D₁.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
      intro z hz
      have hzP : (z : G) ∈ Subgroup.normalizer (P : Set G) := by
        apply mem_normalizer_of_forall_conj_mem
        intro y hy
        exact (Subgroup.mem_normalizer_iff.1 hz ⟨y, hPN hy⟩).1 hy
      have hPc : P.map (MulAut.conj (z : G)).toMonoidHom = P :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1 hzP
      have hD : D₁.map (MulAut.conj (z : G)).toMonoidHom = D₁ := by
        have h1 : GomiD P (D₁.map (MulAut.conj (z : G)).toMonoidHom) := by
          have := hD₁.map_conj (z : G)
          rwa [hPc] at this
        exact hex _ h1
      have hzD : (z : G) ∈ Subgroup.normalizer (D₁ : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.2 hD
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact Subgroup.mem_normalizer_iff.1 hzD (y : G)
    rcases hirr (D₁.subgroupOf N) (fun x hx => hD₁.1.2 hx) hNT with h | h
    · have : D₁ ≤ H := fun x hx => h (show (⟨x, hDN hx⟩ : N) ∈ D₁.subgroupOf N from hx)
      exact hHD.not_ge this
    · have hH1 : H.subgroupOf N ≤ D₁.subgroupOf N := fun x hx => hHD.le hx
      have h2 : D₁.subgroupOf N = P.subgroupOf N := by
        rw [← h]
        exact (sup_eq_left.2 hH1).symm
      have : P ≤ D₁ := fun x hx => by
        have hx' : (⟨x, hPN hx⟩ : N) ∈ P.subgroupOf N := hx
        rw [← h2] at hx'
        exact hx'
      exact hDP.not_ge this

end Main

end Gomi41

theorem exists_gomiE [Finite G]
    (hO : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    (hc : CFSG.Assembly.IsCharTwoType G)
    (hi : ∀ H : Subgroup G, GomiH H → ∀ S : Subgroup G,
      IsSylowOf 2 S (Subgroup.normalizer (H : Set G)) → ClassLETwo S)
    (hZ : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ClassLETwo S →
      ∀ z ∈ S, (∀ y ∈ S, y * z = z * y) → z * z = 1)
    {P D₁ : Subgroup G} (hP : IsSylowOf 2 P ⊤) (hD₁ : GomiD P D₁) :
    ∃ D₂ : Subgroup G, GomiE P D₁ D₂ := by
  by_cases hnorm : P ≤ Subgroup.normalizer (D₁ : Set G)
  · exact Gomi41.exists_gomiE_of_normal hO hO2 hc hi hZ hP hD₁ hnorm
  · exact Gomi41.exists_gomiE_of_not_normal hP hD₁ hnorm

end CFSG.CGT.PushingUpLit.C2L
