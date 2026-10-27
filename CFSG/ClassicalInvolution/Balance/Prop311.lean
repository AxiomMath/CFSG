module

public import CFSG.Assembly.OddCoreSpan

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification

section OddCoreCentralizer

variable {X : Type*} [Group X]

@[expose] def oddCoreCentralizer (B : Subgroup X) : Subgroup X :=
  (componentClassificationOddCore (Subgroup.centralizer (B : Set X))).map
    (Subgroup.centralizer (B : Set X)).subtype

theorem oddCoreCentralizer_le_centralizer (B : Subgroup X) :
    oddCoreCentralizer B ≤ Subgroup.centralizer (B : Set X) :=
  Subgroup.map_subtype_le _

theorem odd_card_oddCoreCentralizer [Finite X] (B : Subgroup X) :
    Odd (Nat.card (oddCoreCentralizer B)) := by
  rw [oddCoreCentralizer,
    Subgroup.card_map_of_injective (Subgroup.centralizer (B : Set X)).subtype_injective]
  exact OddCore.odd_card _

theorem le_oddCoreCentralizer {B S : Subgroup X} (hS : S ≤ Subgroup.centralizer (B : Set X))
    (hnorm : ∀ c ∈ Subgroup.centralizer (B : Set X), ∀ s ∈ S, c * s * c⁻¹ ∈ S)
    (hodd : Odd (Nat.card S)) : S ≤ oddCoreCentralizer B := by
  set C := Subgroup.centralizer (B : Set X) with hC
  have hN : (S.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hS]
    exact fun h k hh hk => hnorm k hk h hh
  have hcard : Odd (Nat.card (S.subgroupOf C)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv]
  have h1 := Subgroup.map_mono (f := C.subtype) (OddCore.maximal C (S.subgroupOf C) hN hcard)
  rwa [Subgroup.map_subgroupOf_eq_of_le hS] at h1

theorem conj_mem_oddCoreCentralizer_of_mem_centralizer {B : Subgroup X} {c : X}
    (hc : c ∈ Subgroup.centralizer (B : Set X)) {u : X} (hu : u ∈ oddCoreCentralizer B) :
    c * u * c⁻¹ ∈ oddCoreCentralizer B := by
  obtain ⟨u', hu', rfl⟩ := hu
  exact ⟨⟨c, hc⟩ * u' * ⟨c, hc⟩⁻¹,
    (componentClassificationOddCore_normal _).conj_mem u' hu' ⟨c, hc⟩, rfl⟩

theorem conj_mem_centralizer_of_mem_normalizer {B : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (B : Set X)) {c : X}
    (hc : c ∈ Subgroup.centralizer (B : Set X)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (B : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh1 : g⁻¹ * h * g ∈ B := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) h).mp hh
    simpa using this
  have hcomm : (g⁻¹ * h * g) * c = c * (g⁻¹ * h * g) := Subgroup.mem_centralizer_iff.mp hc _ hh1
  calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * c * g⁻¹) * h := by group

theorem conj_mem_oddCoreCentralizer [Finite X] {B : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (B : Set X)) {u : X} (hu : u ∈ oddCoreCentralizer B) :
    g * u * g⁻¹ ∈ oddCoreCentralizer B := by
  have key : (oddCoreCentralizer B).map (MulAut.conj g).toMonoidHom ≤ oddCoreCentralizer B := by
    apply le_oddCoreCentralizer
    · rintro _ ⟨v, hv, rfl⟩
      exact conj_mem_centralizer_of_mem_normalizer hg (oddCoreCentralizer_le_centralizer B hv)
    · rintro c hc _ ⟨v, hv, rfl⟩
      have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer (B : Set X) := by
        have := conj_mem_centralizer_of_mem_normalizer (inv_mem hg) hc
        simpa using this
      refine ⟨(g⁻¹ * c * g) * v * (g⁻¹ * c * g)⁻¹,
        conj_mem_oddCoreCentralizer_of_mem_centralizer hc' hv, ?_⟩
      show g * ((g⁻¹ * c * g) * v * (g⁻¹ * c * g)⁻¹) * g⁻¹ = c * (g * v * g⁻¹) * c⁻¹
      group
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact odd_card_oddCoreCentralizer B
  exact key ⟨u, hu, rfl⟩

theorem oddCoreCentralizer_le_sup_zpowers [Finite X] {N : Subgroup X} [N.Normal] {A : Subgroup X}
    {b : X} (hb : b ∈ Subgroup.normalizer (A : Set X)) (hb2 : b * b ∈ A) (hbN : b ∈ A ⊔ N) :
    oddCoreCentralizer A ≤ oddCoreCentralizer (A ⊔ Subgroup.zpowers b) ⊔ N := by
  intro u hu
  set U := oddCoreCentralizer A with hU
  have hUC : ∀ x ∈ U, ∀ a ∈ A, a * x = x * a := fun x hx a ha =>
    Subgroup.mem_centralizer_iff.mp (oddCoreCentralizer_le_centralizer A hx) a ha
  obtain ⟨a, ha, n, hn, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hbN
  have hbU : ∀ x ∈ U, b⁻¹ * x * b ∈ U := fun x hx => by
    have := conj_mem_oddCoreCentralizer (inv_mem hb) hx
    simpa using this
  set w : X := u⁻¹ * (b⁻¹ * u * b) with hw
  have hwU : w ∈ U := mul_mem (inv_mem hu) (hbU u hu)
  have hwN : w ∈ N := by
    have h0 : a⁻¹ * u * a = u := by
      rw [mul_assoc, ← hUC u hu a ha, inv_mul_cancel_left]
    have h1 : b⁻¹ * u * b = n⁻¹ * u * n := by
      rw [← hab]
      calc (a * n)⁻¹ * u * (a * n) = n⁻¹ * (a⁻¹ * u * a) * n := by group
        _ = n⁻¹ * u * n := by rw [h0]
    have h2 : w = (u⁻¹ * n⁻¹ * u⁻¹⁻¹) * n := by
      rw [hw, h1]
      group
    rw [h2]
    exact mul_mem (‹N.Normal›.conj_mem n⁻¹ (inv_mem hn) u⁻¹) hn
  have hbb : b⁻¹ * b⁻¹ * u * b * b = u := by
    have h3 : (b * b) * u = u * (b * b) := hUC u hu (b * b) hb2
    calc b⁻¹ * b⁻¹ * u * b * b = (b * b)⁻¹ * (u * (b * b)) := by group
      _ = (b * b)⁻¹ * ((b * b) * u) := by rw [h3]
      _ = u := by rw [inv_mul_cancel_left]
  have hwinv : b⁻¹ * w * b = w⁻¹ := by
    calc b⁻¹ * w * b = (b⁻¹ * u * b)⁻¹ * (b⁻¹ * b⁻¹ * u * b * b) := by rw [hw]; group
      _ = (b⁻¹ * u * b)⁻¹ * u := by rw [hbb]
      _ = w⁻¹ := by rw [hw]; group
  have hord : Odd (orderOf w) := by
    have hdvd : orderOf w ∣ Nat.card U := by
      have := orderOf_dvd_natCard (⟨w, hwU⟩ : U)
      rwa [← Subgroup.orderOf_coe (⟨w, hwU⟩ : U)] at this
    exact (odd_card_oddCoreCentralizer A).of_dvd_nat hdvd
  obtain ⟨k, hk⟩ := hord
  set v : X := w ^ (k + 1) with hv
  have hvv : v * v = w := by
    rw [hv, ← pow_add]
    have : k + 1 + (k + 1) = orderOf w + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hvU : v ∈ U := pow_mem hwU _
  have hvN : v ∈ N := pow_mem hwN _
  have hvinv : b⁻¹ * v * b = v⁻¹ := by
    have := conj_pow (a := b⁻¹) (b := w) (i := k + 1)
    simp only [inv_inv] at this
    rw [hv, ← this, hwinv, inv_pow]
  set y : X := u * v with hy
  have hyU : y ∈ U := mul_mem hu hvU
  have hbu : b⁻¹ * u * b = u * w := by rw [hw]; group
  have hyb : b⁻¹ * y * b = y := by
    calc b⁻¹ * y * b = (b⁻¹ * u * b) * (b⁻¹ * v * b) := by rw [hy]; group
      _ = (u * (v * v)) * v⁻¹ := by rw [hbu, hvinv, hvv]
      _ = y := by rw [hy]; group
  have hyc : y ∈ Subgroup.centralizer ((A ⊔ Subgroup.zpowers b : Subgroup X) : Set X) := by
    have hle : A ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer {y} := by
      refine sup_le (fun a' ha' => ?_) ((Subgroup.zpowers_le).mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hUC y hyU a' ha')
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have : y * b = b * y := by
          calc y * b = b * (b⁻¹ * y * b) := by group
            _ = b * y := by rw [hyb]
        exact this.symm
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hh))
  have hyU1 : y ∈ oddCoreCentralizer (A ⊔ Subgroup.zpowers b) := by
    have hsub : U ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers b : Subgroup X) : Set X) ≤
        oddCoreCentralizer (A ⊔ Subgroup.zpowers b) := by
      apply le_oddCoreCentralizer inf_le_right
      · intro c hc s hs
        have hcA : c ∈ Subgroup.centralizer (A : Set X) :=
          Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hc
        have hc2 : c * s * c⁻¹ ∈
            Subgroup.centralizer ((A ⊔ Subgroup.zpowers b : Subgroup X) : Set X) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hs.2) (Subgroup.inv_mem _ hc)
        exact ⟨conj_mem_oddCoreCentralizer_of_mem_centralizer hcA hs.1, hc2⟩
      · exact (odd_card_oddCoreCentralizer A).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    exact hsub ⟨hyU, hyc⟩
  have hu' : u = y * v⁻¹ := by rw [hy]; group
  rw [hu']
  exact mul_mem (Subgroup.mem_sup_left hyU1) (Subgroup.mem_sup_right (inv_mem hvN))

theorem exists_index_two_normal_of_lt [Finite X] {B P : Subgroup X} (hP : IsPGroup 2 P)
    (hBP : B < P) :
    ∃ P₁ : Subgroup X, B ≤ P₁ ∧ P₁ < P ∧ ∃ b ∈ P, b ∈ Subgroup.normalizer (P₁ : Set X) ∧
      b * b ∈ P₁ ∧ P₁ ⊔ Subgroup.zpowers b = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hne : B.subgroupOf P ≠ ⊤ := fun h => (ne_of_lt hBP) (le_antisymm hBP.le
    (fun x hx => (Subgroup.mem_subgroupOf).mp (h ▸ Subgroup.mem_top (⟨x, hx⟩ : P))))
  obtain ⟨Q, hQ, hBQ⟩ : ∃ Q : Subgroup P, IsCoatom Q ∧ B.subgroupOf P ≤ Q := by
    rcases eq_top_or_exists_le_coatom (B.subgroupOf P) with h | h
    · exact absurd h hne
    · exact h
  have hidx : Q.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hP).mp hQ
  have : Q.Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨b', hb'⟩ : ∃ b' : P, b' ∉ Q := by
    by_contra h
    push Not at h
    exact hQ.1 ((Subgroup.eq_top_iff' Q).mpr h)
  have hmem : ∀ x : X, x ∈ Q.map P.subtype ↔ ∃ q ∈ Q, (q : X) = x := fun x => by
    simp [Subgroup.mem_map]
  refine ⟨Q.map P.subtype, ?_, ?_, (b' : X), b'.2, ?_, ?_, ?_⟩
  · intro x hx
    exact (hmem x).mpr ⟨⟨x, hBP.le hx⟩, hBQ ((Subgroup.mem_subgroupOf).mpr hx), rfl⟩
  · refine lt_of_le_of_ne (Subgroup.map_subtype_le Q) fun h => hQ.1 ?_
    refine (Subgroup.eq_top_iff' Q).mpr fun p => ?_
    have : (p : X) ∈ Q.map P.subtype := by rw [h]; exact p.2
    obtain ⟨q, hq, hqp⟩ := (hmem _).mp this
    exact (Subtype.ext hqp : q = p) ▸ hq
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨q, hq, rfl⟩ := (hmem h).mp hh
      exact (hmem _).mpr ⟨b' * q * b'⁻¹, Subgroup.Normal.conj_mem inferInstance q hq b', rfl⟩
    · intro hh
      obtain ⟨q, hq, hqh⟩ := (hmem _).mp hh
      have hh' : h = ((b'⁻¹ * q * b' : P) : X) := by
        have : (b' : X) * h * (b' : X)⁻¹ = q := hqh.symm
        calc h = (b' : X)⁻¹ * ((b' : X) * h * (b' : X)⁻¹) * b' := by group
          _ = ((b'⁻¹ * q * b' : P) : X) := by rw [this]; rfl
      rw [hh']
      exact (hmem _).mpr ⟨b'⁻¹ * q * b', by
        simpa using Subgroup.Normal.conj_mem inferInstance q hq b'⁻¹, rfl⟩
  · have h2 : b' ^ 2 ∈ Q := by
      have := Subgroup.pow_index_mem Q b'
      rwa [hidx] at this
    exact (hmem _).mpr ⟨b' * b', by simpa [sq] using h2, rfl⟩
  · refine le_antisymm (sup_le (Subgroup.map_subtype_le Q)
      ((Subgroup.zpowers_le).mpr b'.2)) ?_
    set R : Subgroup P := (Q.map P.subtype ⊔ Subgroup.zpowers (b' : X)).subgroupOf P with hR
    have hQR : Q < R := by
      refine lt_of_le_of_ne (fun q hq => ?_) fun h => hb' ?_
      · exact (Subgroup.mem_subgroupOf).mpr
          (Subgroup.mem_sup_left ((hmem _).mpr ⟨q, hq, rfl⟩))
      · rw [h]
        exact (Subgroup.mem_subgroupOf).mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have hRtop : R = ⊤ := hQ.lt_iff.mp hQR
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ R := hRtop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf).mp this

theorem oddCoreCentralizer_le_sup_of_le [Finite X] {N : Subgroup X} [N.Normal] :
    ∀ (n : ℕ) {B P : Subgroup X}, Nat.card P ≤ n → B ≤ P → IsPGroup 2 P → P ≤ B ⊔ N →
      oddCoreCentralizer B ≤ oddCoreCentralizer P ⊔ N := by
  intro n
  induction n with
  | zero =>
    intro B P hn
    have := Nat.card_pos (α := P)
    omega
  | succ n ih =>
    intro B P hn hBP hP hPN
    rcases eq_or_lt_of_le hBP with rfl | hlt
    · exact le_sup_left
    · obtain ⟨P₁, hBP₁, hP₁P, b, hbP, hbn, hbb, hsup⟩ := exists_index_two_normal_of_lt hP hlt
      have hcard : Nat.card P₁ ≤ n := by
        have h1 : Nat.card P₁ ≤ Nat.card P := Subgroup.card_le_of_le hP₁P.le
        have h2 : Nat.card P₁ ≠ Nat.card P := fun h =>
          (ne_of_lt hP₁P) (Subgroup.eq_of_le_of_card_ge hP₁P.le h.symm.le)
        omega
      have hP₁N : P₁ ≤ B ⊔ N := hP₁P.le.trans hPN
      have h1 := ih hcard hBP₁ (IsPGroup.to_le hP hP₁P.le) hP₁N
      have hbN : b ∈ P₁ ⊔ N := (sup_le_sup_right hBP₁ N) (hPN hbP)
      have h2 := oddCoreCentralizer_le_sup_zpowers (N := N) hbn hbb hbN
      rw [hsup] at h2
      exact h1.trans (sup_le h2 le_sup_right)

theorem exists_mul_mem_normalizer_of_commutator_mem [Finite X] {N B T : Subgroup X} [N.Normal]
    (hT : T = B ⊔ N)
    (S : Sylow 2 T) (hBS : B.subgroupOf T ≤ S) {y : X}
    (hy : ∀ b ∈ B, y * b * y⁻¹ * b⁻¹ ∈ N) :
    ∃ n ∈ N, n⁻¹ * y ∈ Subgroup.normalizer
      (((S : Subgroup T).map T.subtype : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBT : B ≤ T := hT ▸ le_sup_left
  have hNT : N ≤ T := hT ▸ le_sup_right
  set P : Subgroup X := (S : Subgroup T).map T.subtype with hP
  have hPT : P ≤ T := Subgroup.map_subtype_le _
  have hBP : B ≤ P := fun b hb => ⟨⟨b, hBT hb⟩,
    hBS ((Subgroup.mem_subgroupOf).mpr hb), rfl⟩
  have hP2 : IsPGroup 2 P := S.isPGroup'.map _
  have hyT : ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
    intro t ht
    rw [hT] at ht
    obtain ⟨b, hb, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ht
    have h1 : y * b * y⁻¹ ∈ T := by
      have : y * b * y⁻¹ = (y * b * y⁻¹ * b⁻¹) * b := by group
      rw [this]
      exact mul_mem (hNT (hy b hb)) (hBT hb)
    have h2 : y * n * y⁻¹ ∈ T := hNT (‹N.Normal›.conj_mem n hn y)
    have : y * (b * n) * y⁻¹ = (y * b * y⁻¹) * (y * n * y⁻¹) := by group
    rw [this]
    exact mul_mem h1 h2
  set P' : Subgroup X := P.map (MulAut.conj y).toMonoidHom with hP'
  have hP'T : P' ≤ T := by
    rintro _ ⟨p, hp, rfl⟩
    exact hyT p (hPT hp)
  have hP'2 : IsPGroup 2 (P'.subgroupOf T) :=
    (hP2.map _).comap_of_injective _ T.subtype_injective
  obtain ⟨S₂, hS₂⟩ := IsPGroup.exists_le_sylow hP'2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥T) S S₂
  have hconj : ∀ x ∈ P, ∃ s ∈ P, (g : X) * s * (g : X)⁻¹ = y * x * y⁻¹ := by
    intro x hx
    have hxS : (⟨y * x * y⁻¹, hyT x (hPT hx)⟩ : T) ∈ (S₂ : Subgroup T) :=
      hS₂ ((Subgroup.mem_subgroupOf).mpr ⟨x, hx, rfl⟩)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxS
    obtain ⟨s, hs, hsx⟩ := hxS
    refine ⟨s, ⟨s, hs, rfl⟩, ?_⟩
    have := congrArg Subtype.val hsx
    simpa [MulAut.smul_def] using this
  set m : X := (g : X)⁻¹ * y with hm
  have hmP : ∀ x ∈ P, m * x * m⁻¹ ∈ P := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := hconj x hx
    have : m * x * m⁻¹ = s := by
      calc m * x * m⁻¹ = (g : X)⁻¹ * (y * x * y⁻¹) * (g : X) := by rw [hm]; group
        _ = (g : X)⁻¹ * ((g : X) * s * (g : X)⁻¹) * (g : X) := by rw [hsx]
        _ = s := by group
    rw [this]
    exact hs
  have hmnorm : m ∈ Subgroup.normalizer (P : Set X) := by
    have hle : P.map (MulAut.conj m).toMonoidHom ≤ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact hmP x hx
    have heq : P.map (MulAut.conj m).toMonoidHom = P := by
      have hc : Nat.card (P.map (MulAut.conj m).toMonoidHom) = Nat.card P :=
        Subgroup.card_map_of_injective (MulAut.conj m).injective
      exact Subgroup.eq_of_le_of_card_ge hle hc.ge
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hmP h hh
    · intro hh
      have : m * h * m⁻¹ ∈ P.map (MulAut.conj m).toMonoidHom := by rw [heq]; exact hh
      obtain ⟨x, hx, hxh⟩ := this
      have : x = h := (MulAut.conj m).injective hxh
      rw [← this]
      exact hx
  have hgNP : (g : X) ∈ N ⊔ P := by
    have : (g : X) ∈ T := g.2
    have hTle : T ≤ N ⊔ P := by
      rw [hT]
      exact sup_le (hBP.trans le_sup_right) le_sup_left
    exact hTle this
  obtain ⟨n, hn, p, hp, hnp⟩ := Subgroup.mem_sup_of_normal_left.mp hgNP
  refine ⟨n, hn, ?_⟩
  have : n⁻¹ * y = p * m := by
    rw [hm, ← hnp]
    group
  rw [this]
  exact mul_mem (Subgroup.le_normalizer hp) hmnorm

theorem map_oddCoreCentralizer_le [Finite X] {Z : Type*} [Group Z] (φ : X →* Z)
    (hφ : Function.Surjective φ) {B : Subgroup X} (hB : IsPGroup 2 B) :
    (oddCoreCentralizer B).map φ ≤ oddCoreCentralizer (B.map φ) := by
  have : Finite Z := Finite.of_surjective φ hφ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup X := φ.ker with hN
  set T : Subgroup X := B ⊔ N with hT
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (p := 2) (P := B.subgroupOf T)
    (hB.comap_of_injective _ T.subtype_injective)
  set P : Subgroup X := (S : Subgroup T).map T.subtype with hP
  have hBT : B ≤ T := le_sup_left
  have hPT : P ≤ T := Subgroup.map_subtype_le _
  have hBP : B ≤ P := fun b hb => ⟨⟨b, hBT hb⟩, hS ((Subgroup.mem_subgroupOf).mpr hb), rfl⟩
  have hP2 : IsPGroup 2 P := S.isPGroup'.map _
  have hchain := oddCoreCentralizer_le_sup_of_le (N := N) _ le_rfl hBP hP2 hPT
  have hsub : (oddCoreCentralizer P).map φ ≤ oddCoreCentralizer (B.map φ) := by
    apply le_oddCoreCentralizer
    · rintro _ ⟨u, hu, rfl⟩
      have huB : u ∈ Subgroup.centralizer (B : Set X) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBP)
          (oddCoreCentralizer_le_centralizer P hu)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp huB b hb]
    · rintro c hc _ ⟨u, hu, rfl⟩
      obtain ⟨y, rfl⟩ := hφ c
      have hy : ∀ b ∈ B, y * b * y⁻¹ * b⁻¹ ∈ N := by
        intro b hb
        have := Subgroup.mem_centralizer_iff.mp hc (φ b) ⟨b, hb, rfl⟩
        rw [hN, MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact this.symm
      obtain ⟨n, hn, hnorm⟩ :=
        exists_mul_mem_normalizer_of_commutator_mem (N := N) (B := B) (T := T) rfl S hS hy
      have hnormP : n⁻¹ * y ∈ Subgroup.normalizer (P : Set X) := hnorm
      refine ⟨(n⁻¹ * y) * u * (n⁻¹ * y)⁻¹, conj_mem_oddCoreCentralizer hnormP hu, ?_⟩
      have hn1 : φ n = 1 := by
        rw [hN] at hn
        exact MonoidHom.mem_ker.mp hn
      simp only [map_mul, map_inv, inv_one, one_mul, hn1]
    · exact (odd_card_oddCoreCentralizer P).of_dvd_nat (Subgroup.card_map_dvd _ _)
  calc (oddCoreCentralizer B).map φ ≤ (oddCoreCentralizer P ⊔ N).map φ := Subgroup.map_mono hchain
    _ = (oddCoreCentralizer P).map φ := by
      have hNbot : N.map φ = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
      rw [Subgroup.map_sup, hNbot, sup_bot_eq]
    _ ≤ _ := hsub

theorem centralizer_zpowers_eq (a : X) :
    Subgroup.centralizer ((Subgroup.zpowers a : Subgroup X) : Set X) =
      Subgroup.centralizer ({a} : Set X) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
  constructor
  · exact fun h => h a (Subgroup.mem_zpowers a)
  · intro h g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((Commute.zpow_left (show Commute a x from h) k).eq)

theorem involutionOddCore_eq_oddCoreCentralizer (a : X) :
    CFSG.Assembly.Dichotomy.involutionOddCore a = oddCoreCentralizer (Subgroup.zpowers a) := by
  unfold CFSG.Assembly.Dichotomy.involutionOddCore oddCoreCentralizer
  rw [centralizer_zpowers_eq]
  rfl

theorem conj_mem_involutionOddCore {a c u : X} (hc : c ∈ Subgroup.centralizer ({a} : Set X))
    (hu : u ∈ CFSG.Assembly.Dichotomy.involutionOddCore a) :
    c * u * c⁻¹ ∈ CFSG.Assembly.Dichotomy.involutionOddCore a := by
  rw [involutionOddCore_eq_oddCoreCentralizer] at hu ⊢
  exact conj_mem_oddCoreCentralizer_of_mem_centralizer (by rwa [centralizer_zpowers_eq]) hu

theorem map_involutionOddCore_le [Finite X] {Z : Type*} [Group Z] (φ : X →* Z)
    (hφ : Function.Surjective φ) {a : X} (ha : IsPGroup 2 (Subgroup.zpowers a)) :
    (CFSG.Assembly.Dichotomy.involutionOddCore a).map φ ≤
      CFSG.Assembly.Dichotomy.involutionOddCore (φ a) := by
  rw [involutionOddCore_eq_oddCoreCentralizer, involutionOddCore_eq_oddCoreCentralizer]
  have := map_oddCoreCentralizer_le φ hφ ha
  rwa [MonoidHom.map_zpowers] at this

theorem map_mk_oddCoreCentralizer_le [Finite X] (N : Subgroup X) [N.Normal] {B : Subgroup X}
    (hB : IsPGroup 2 B) :
    (oddCoreCentralizer B).map (QuotientGroup.mk' N) ≤
      oddCoreCentralizer (B.map (QuotientGroup.mk' N)) :=
  map_oddCoreCentralizer_le (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hB

omit [Group X] in
theorem isPGroup_zpowers_of_mul_self_eq_one {Y : Type*} [Group Y] [Finite Y] {f : Y}
    (hf2 : f * f = 1) : IsPGroup 2 (Subgroup.zpowers f) := by
  rw [IsPGroup.iff_card, Nat.card_zpowers]
  have h2 : orderOf f ∣ 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [sq, hf2])
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  exact ⟨i, hi⟩

end OddCoreCentralizer

end CFSG.ClassicalInvolution.Balance
