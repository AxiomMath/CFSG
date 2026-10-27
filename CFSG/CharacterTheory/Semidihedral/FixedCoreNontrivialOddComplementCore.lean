module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialOddComplement
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialCore
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialSetup
public import CFSG.CharacterTheory.Semidihedral.Principal.ConfinedInvertedOddSubgroup

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open Subgroup

variable {G : Type*} [Group G]

namespace LocalData

variable {t s d : G} {J B W : Subgroup G} (h : LocalData t s d J B W)
include h

theorem commute_B_of_mem_sup {x y : G} (hx : x ∈ J ⊔ B) (hy : y ∈ B) : x * y = y * x := by
  obtain ⟨j, hj, b, hb, rfl⟩ := exists_mul_of_mem_sup h.JB_comm hx
  rw [mul_assoc, h.B_comm b hb y hy, ← mul_assoc, h.JB_comm j hj y hy, mul_assoc]

theorem eq_t_of_centralizes_B (hB : B ≠ ⊥) {u : G} (huC : u ∈ centralizer ({t} : Set G))
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huB : ∀ x ∈ B, u * x = x * u) : u = t := by
  obtain ⟨x, hx, y, hy, hc | hc⟩ := h.cover u huC
  · have hxy : x * y = y * x := h.JB_comm x hx y hy
    have h1 : x * x * (y * y) = 1 := by
      rw [← hu2, hc]
      calc x * x * (y * y) = x * (x * y) * y := by group
        _ = x * (y * x) * y := by rw [hxy]
        _ = x * y * (x * y) := by group
    have hyy : y * y ∈ J ⊓ B := by
      refine ⟨?_, B.mul_mem hy hy⟩
      have : y * y = (x * x)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact J.inv_mem (J.mul_mem hx hx)
    rw [h.JB_disj, mem_bot] at hyy
    have hy1 : y = 1 := eq_one_of_mul_self_eq_one_of_odd (h.B_odd y hy) hyy
    rw [hy1, mul_one] at hc
    rw [hy1, mul_one, mul_one] at h1
    rcases h.J_inv x hx h1 with hx1 | hxt
    · exact absurd (hc.trans hx1) hu1
    · exact hc.trans hxt
  · exfalso
    apply hB
    rw [eq_bot_iff]
    intro b hb
    rw [mem_bot]
    have hinv : u * b * u⁻¹ = b⁻¹ := by
      rw [hc]
      have h1 : s * b * s⁻¹ = b⁻¹ := h.s_inv b hb
      have hxb : x * b⁻¹ = b⁻¹ * x := h.JB_comm x hx _ (B.inv_mem hb)
      have hyb : y * b⁻¹ = b⁻¹ * y := h.B_comm y hy _ (B.inv_mem hb)
      calc x * y * s * b * (x * y * s)⁻¹ = x * y * (s * b * s⁻¹) * y⁻¹ * x⁻¹ := by group
        _ = x * (y * b⁻¹) * y⁻¹ * x⁻¹ := by rw [h1]; group
        _ = x * b⁻¹ * x⁻¹ := by rw [hyb]; group
        _ = b⁻¹ := by rw [hxb]; group
    have hcomm : u * b * u⁻¹ = b := by rw [huB b hb]; group
    rw [hcomm] at hinv
    exact eq_one_of_mul_self_eq_one_of_odd (h.B_odd b hb)
      (by calc b * b = b⁻¹ * b := by rw [← hinv]
            _ = 1 := inv_mul_cancel b)

theorem conj_eq_of_mem_sup
    (hconf : ∀ u ∈ B, u ≠ 1 → centralizer ({u} : Set G) ≤ centralizer ({t} : Set G))
    {x g : G} (hx : x ∈ B) (hg : Odd (orderOf g)) (hy : g⁻¹ * x * g ∈ J ⊔ B) :
    g⁻¹ * x * g = x := by
  by_cases hx1 : x = 1
  · rw [hx1]; group
  have hB : B ≠ ⊥ := fun hB => hx1 (by rw [hB] at hx; exact mem_bot.mp hx)
  have ht'B : ∀ b ∈ B, (g⁻¹ * t * g) * b = b * (g⁻¹ * t * g) := by
    intro b hb
    have h1 : (g⁻¹ * x * g) * b = b * (g⁻¹ * x * g) := h.commute_B_of_mem_sup hy hb
    have h2 : g * b * g⁻¹ ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * b * g⁻¹ * x = g * (b * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * b) * g⁻¹ := by rw [h1]
        _ = x * (g * b * g⁻¹) := by group
    have h3 := hconf x hx hx1 h2
    rw [mem_centralizer_singleton_iff] at h3
    calc (g⁻¹ * t * g) * b = g⁻¹ * (t * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * t) * g := by rw [h3]
      _ = b * (g⁻¹ * t * g) := by group
  have ht'C : g⁻¹ * t * g ∈ centralizer ({t} : Set G) := by
    apply hconf x hx hx1
    rw [mem_centralizer_singleton_iff]
    exact ht'B x hx
  have ht'2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [h.t_sq]; group
  have ht'1 : g⁻¹ * t * g ≠ 1 := by
    intro h1
    apply h.t_ne_one
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have ht' := h.eq_t_of_centralizes_B hB ht'C ht'2 ht'1 ht'B
  have hgC : g ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g * t = g * (g⁻¹ * t * g) := by rw [ht']
      _ = t * g := by group
  have hgx : g * x = x * g := h.commute_B_of_mem_sup (h.odd_mem g hgC hg) hx
  calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
    _ = g⁻¹ * (g * x) := by rw [hgx]
    _ = x := by group

theorem commutator_mem_J {a b : G} (ha : a ∈ J ⊔ B) (hb : b ∈ J ⊔ B) :
    a * b * a⁻¹ * b⁻¹ ∈ J := by
  obtain ⟨j₁, hj₁, b₁, hb₁, rfl⟩ := exists_mul_of_mem_sup h.JB_comm ha
  obtain ⟨j₂, hj₂, b₂, hb₂, rfl⟩ := exists_mul_of_mem_sup h.JB_comm hb
  have e1 : b₁ * j₂ = j₂ * b₁ := (h.JB_comm j₂ hj₂ b₁ hb₁).symm
  have e2 : b₁ * b₂ = b₂ * b₁ := h.B_comm b₁ hb₁ b₂ hb₂
  have e5 : b₂ * j₁⁻¹ = j₁⁻¹ * b₂ := (h.JB_comm _ (J.inv_mem hj₁) b₂ hb₂).symm
  have key : j₁ * b₁ * (j₂ * b₂) * (j₁ * b₁)⁻¹ * (j₂ * b₂)⁻¹ =
      j₁ * j₂ * j₁⁻¹ * j₂⁻¹ := by
    calc j₁ * b₁ * (j₂ * b₂) * (j₁ * b₁)⁻¹ * (j₂ * b₂)⁻¹
        = j₁ * (b₁ * j₂) * b₂ * b₁⁻¹ * j₁⁻¹ * b₂⁻¹ * j₂⁻¹ := by group
      _ = j₁ * (j₂ * b₁) * b₂ * b₁⁻¹ * j₁⁻¹ * b₂⁻¹ * j₂⁻¹ := by rw [e1]
      _ = j₁ * j₂ * (b₁ * b₂) * b₁⁻¹ * j₁⁻¹ * b₂⁻¹ * j₂⁻¹ := by group
      _ = j₁ * j₂ * (b₂ * b₁) * b₁⁻¹ * j₁⁻¹ * b₂⁻¹ * j₂⁻¹ := by rw [e2]
      _ = j₁ * j₂ * (b₂ * j₁⁻¹) * b₂⁻¹ * j₂⁻¹ := by group
      _ = j₁ * j₂ * (j₁⁻¹ * b₂) * b₂⁻¹ * j₂⁻¹ := by rw [e5]
      _ = j₁ * j₂ * j₁⁻¹ * j₂⁻¹ := by group
  rw [key]
  exact J.mul_mem (J.mul_mem (J.mul_mem hj₁ hj₂) (J.inv_mem hj₁)) (J.inv_mem hj₂)

theorem isPGroup_zpowers_of_mul {ℓ : ℕ} [Fact ℓ.Prime] {j b : G} (hj : j ∈ J) (hb : b ∈ B)
    (hjb : IsPGroup ℓ (zpowers (j * b))) : IsPGroup ℓ (zpowers b) := by
  obtain ⟨n, hn⟩ := hjb ⟨j * b, mem_zpowers _⟩
  have hn' : (j * b) ^ ℓ ^ n = 1 := congrArg Subtype.val hn
  have hcomm : Commute j b := h.JB_comm j hj b hb
  rw [hcomm.mul_pow] at hn'
  have hbJ : b ^ ℓ ^ n ∈ J ⊓ B := by
    refine ⟨?_, B.pow_mem hb _⟩
    rw [eq_inv_of_mul_eq_one_right hn']
    exact J.inv_mem (J.pow_mem hj _)
  rw [h.JB_disj, mem_bot] at hbJ
  refine IsPGroup.of_card_dvd_pow (n := n) ?_
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one hbJ

theorem exists_normal_complement_sylow [Finite G]
    (hconf : ∀ u ∈ B, u ≠ 1 → centralizer ({u} : Set G) ≤ centralizer ({t} : Set G))
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {P : Subgroup G} (hPB : P ≤ B) (hP : IsPGroup ℓ P)
    (hPmax : ∀ x ∈ B, IsPGroup ℓ (zpowers x) → x ∈ P)
    (hN : ∀ Q : Subgroup G, Q ≤ centralizer ({t} : Set G) → IsPGroup ℓ Q → P ≤ Q →
      normalizer (Q : Set G) ≤ centralizer ({t} : Set G))
    {R : Subgroup G} (hR : Odd (Nat.card R)) (hBR : B ≤ R) :
    ∃ M : Subgroup R, M.Normal ∧ Disjoint M (P.subgroupOf R) ∧ M.index ≤ Nat.card P := by
  classical
  have hPR : P ≤ R := hPB.trans hBR
  obtain ⟨Q₀, hPQ₀⟩ := (hP.comap_subtype (K := R)).exists_le_sylow
  set Q : Subgroup G := (Q₀ : Subgroup R).map R.subtype with hQdef
  have hQp : IsPGroup ℓ Q := Q₀.isPGroup'.map R.subtype
  have hPQ : P ≤ Q := fun x hx => ⟨⟨x, hPR hx⟩, hPQ₀ hx, rfl⟩
  have hQR : Q ≤ R := map_subtype_le _
  have hoddR : ∀ x ∈ R, Odd (orderOf x) := fun x hx =>
    hR.of_dvd_nat (Subgroup.orderOf_dvd_natCard R hx)
  have hQC : Q ≤ centralizer ({t} : Set G) := by
    have hQ'p : IsPGroup ℓ (Q ⊓ centralizer ({t} : Set G) : Subgroup G) := hQp.to_le inf_le_left
    have hPQ' : P ≤ Q ⊓ centralizer ({t} : Set G) := le_inf hPQ (hPB.trans h.B_le)
    have hNQ' := hN _ inf_le_right hQ'p hPQ'
    by_contra hne
    have hne' : (Q ⊓ centralizer ({t} : Set G) : Subgroup G) ≠ Q := fun heq =>
      hne (heq ▸ inf_le_right)
    obtain ⟨y, hyQ, hyN, hyQ'⟩ := exists_mem_normalizer_not_mem_of_isPGroup hQp inf_le_left hne'
    exact hyQ' ⟨hyQ, hNQ' hyN⟩
  have hQJB : Q ≤ J ⊔ B := fun x hx => h.odd_mem x (hQC hx) (hoddR x (hQR hx))
  have hmemQ : ∀ y : Q₀, ((y : R) : G) ∈ Q := fun y => ⟨(y : R), y.2, rfl⟩
  set Jq : Subgroup Q₀ := J.comap ((R.subtype).comp (Q₀ : Subgroup R).subtype) with hJq
  have hJqmem : ∀ y : Q₀, y ∈ Jq ↔ ((y : R) : G) ∈ J := fun y => Iff.rfl
  have hJqn : Jq.Normal := ⟨fun x hx g => by
    rw [hJqmem] at hx ⊢
    have := h.J_conj _ (hQC (hmemQ g)) _ hx
    simpa using this⟩
  let _ : CommGroup (Q₀ ⧸ Jq) :=
    { (inferInstance : Group (Q₀ ⧸ Jq)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with
        | H x =>
        induction b using QuotientGroup.induction_on with
        | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hJqmem]
        have hx := hQJB (hmemQ x⁻¹)
        have hy := hQJB (hmemQ y⁻¹)
        have := h.commutator_mem_J hy hx
        simpa [mul_assoc] using this }
  set φ : Q₀ →* Q₀ ⧸ Jq := QuotientGroup.mk' Jq with hφ
  set V : R →* Q₀ ⧸ Jq := MonoidHom.transfer φ with hV
  have hkey : ∀ g : R, (g : G) ∈ P → ∀ (k : ℕ) (g₀ : R),
      g₀⁻¹ * g ^ k * g₀ ∈ (Q₀ : Subgroup R) → g₀⁻¹ * g ^ k * g₀ = g ^ k := by
    intro g hg k g₀ hmem
    apply Subtype.ext
    have hx : ((g : G) ^ k) ∈ B := hPB (P.pow_mem hg k)
    have hy : (g₀ : G)⁻¹ * (g : G) ^ k * g₀ ∈ J ⊔ B := by
      have := hQJB ⟨_, hmem, rfl⟩
      simpa using this
    have := h.conj_eq_of_mem_sup hconf hx (hoddR _ g₀.2) hy
    simpa using this
  refine ⟨V.ker, MonoidHom.normal_ker _, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro g ⟨hgM, hgP⟩
    have hgP' : (g : G) ∈ P := hgP
    have hgM : V g = 1 := hgM
    have h1 := MonoidHom.transfer_eq_pow φ g (hkey g hgP')
    rw [← hV, hgM] at h1
    have h2 : ((g : G) ^ (Q₀ : Subgroup R).index) ∈ J := by
      have h3 := (QuotientGroup.eq_one_iff _).mp h1.symm
      rw [hJqmem] at h3
      simpa using h3
    have h4 : ((g : G) ^ (Q₀ : Subgroup R).index) ∈ J ⊓ B := ⟨h2, hPB (P.pow_mem hgP' _)⟩
    rw [h.JB_disj, mem_bot] at h4
    obtain ⟨n, hn⟩ := hP ⟨g, hgP'⟩
    have hn' : (g : G) ^ ℓ ^ n = 1 := congrArg Subtype.val hn
    have hd1 : orderOf (g : G) ∣ ℓ ^ n := orderOf_dvd_of_pow_eq_one hn'
    have hd2 : orderOf (g : G) ∣ (Q₀ : Subgroup R).index := orderOf_dvd_of_pow_eq_one h4
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hℓ.out).mp hd1
    have hk0 : k = 0 := by
      by_contra hk0
      apply Q₀.not_dvd_index
      rw [hk] at hd2
      exact (dvd_pow_self ℓ hk0).trans hd2
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    rw [mem_bot]
    exact Subtype.ext hk
  · rw [Subgroup.index_ker]
    refine (Subgroup.card_le_card_group _).trans ?_
    let ι : P → Q₀ ⧸ Jq := fun x => φ ⟨⟨x, hPR x.2⟩, hPQ₀ x.2⟩
    refine Nat.card_le_card_of_surjective ι ?_
    intro a
    induction a using QuotientGroup.induction_on with
    | H y =>
    obtain ⟨j, hj, b, hb, hjb⟩ := exists_mul_of_mem_sup h.JB_comm (hQJB (hmemQ y))
    have hyp : IsPGroup ℓ (zpowers ((y : R) : G)) := by
      obtain ⟨n, hn⟩ := Q₀.isPGroup' y
      refine IsPGroup.of_card_dvd_pow (n := n) ?_
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (by
        have := congrArg (fun z : Q₀ => ((z : R) : G)) hn
        simpa using this)
    rw [hjb] at hyp
    have hbP : b ∈ P := hPmax b hb (h.isPGroup_zpowers_of_mul hj hb hyp)
    refine ⟨⟨b, hbP⟩, ?_⟩
    change (QuotientGroup.mk _ : Q₀ ⧸ Jq) = QuotientGroup.mk y
    rw [QuotientGroup.eq, hJqmem]
    change (b : G)⁻¹ * ((y : R) : G) ∈ J
    rw [hjb, h.JB_comm j hj b hb, inv_mul_cancel_left]
    exact hj

theorem odd_normal_complement [Finite G]
    (hconf : ∀ u ∈ B, u ≠ 1 → centralizer ({u} : Set G) ≤ centralizer ({t} : Set G))
    (hN : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card B → ∀ P : Sylow ℓ B, ∀ Q : Subgroup G,
      Q ≤ centralizer ({t} : Set G) → IsPGroup ℓ Q → (P : Subgroup B).map B.subtype ≤ Q →
      normalizer (Q : Set G) ≤ centralizer ({t} : Set G))
    {R : Subgroup G} (hR : Odd (Nat.card R)) (hBR : B ≤ R) :
    ∃ M : Subgroup G, M ≤ R ∧ R ≤ normalizer (M : Set G) ∧ Disjoint M B ∧ M ⊔ B = R ∧
      Nat.card M * Nat.card B = Nat.card R := by
  classical
  have hXcard : Nat.card (B.subgroupOf R) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hBR).toEquiv
  obtain ⟨M', hM'n, hM'⟩ := exists_normal_isComplement'_of_primewise (B.subgroupOf R)
    (fun ℓ hℓ => by
      rw [hXcard] at hℓ ⊢
      have hℓp := Nat.prime_of_mem_primeFactors hℓ
      have : Fact ℓ.Prime := ⟨hℓp⟩
      obtain ⟨P₀⟩ : Nonempty (Sylow ℓ B) := inferInstance
      set P : Subgroup G := (P₀ : Subgroup B).map B.subtype with hPdef
      have hPB : P ≤ B := map_subtype_le _
      have hP : IsPGroup ℓ P := P₀.isPGroup'.map B.subtype
      have hPcard : Nat.card P = ℓ ^ (Nat.card B).factorization ℓ := by
        rw [hPdef, Subgroup.card_map_of_injective B.subtype_injective,
          Sylow.card_eq_multiplicity]
      have hBab : ∀ x y : B, x * y = y * x := fun x y =>
        Subtype.ext (h.B_comm x x.2 y y.2)
      have hP₀n : (P₀ : Subgroup B).Normal := ⟨fun x hx g => by
        rw [hBab g x, mul_inv_cancel_right]; exact hx⟩
      have hPmax : ∀ x ∈ B, IsPGroup ℓ (zpowers x) → x ∈ P := by
        intro x hx hxp
        have hxp' : IsPGroup ℓ (zpowers (⟨x, hx⟩ : B)) := by
          intro y
          obtain ⟨k, hk⟩ := mem_zpowers_iff.mp y.2
          obtain ⟨n, hn⟩ := hxp ⟨x ^ k, zpow_mem (mem_zpowers x) k⟩
          refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
          have := congrArg Subtype.val hn
          simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
          have e : ((y : B) : G) = x ^ k := by rw [← hk]; simp
          rw [e]
          exact this
        obtain ⟨T, hT⟩ := hxp'.exists_le_sylow
        have hu := Sylow.unique_of_normal P₀ hP₀n
        have hTP : T = P₀ := Subsingleton.elim _ _
        exact ⟨⟨x, hx⟩, hTP ▸ hT (mem_zpowers _), rfl⟩
      obtain ⟨M, hMn, hMdisj, hMi⟩ := h.exists_normal_complement_sylow hconf hPB hP hPmax
        (fun Q hQC hQp hPQ => hN ℓ hℓp (Nat.dvd_of_mem_primeFactors hℓ) P₀ Q hQC hQp hPQ)
        hR hBR
      refine ⟨M, hMn, ?_, hMi.trans hPcard.le⟩
      intro hdvd
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
      have hxM : (x : R) ∈ M := (Subgroup.mem_inf.mp x.2).1
      have hxB : ((x : R) : G) ∈ B := (Subgroup.mem_inf.mp x.2).2
      have hxo : orderOf ((x : R) : G) = ℓ := by
        have e1 : orderOf ((x : R) : G) = orderOf (x : R) := Subgroup.orderOf_coe _
        have e2 : orderOf (x : R) = orderOf x := Subgroup.orderOf_coe _
        rw [e1, e2, hx]
      have hxP : ((x : R) : G) ∈ P := hPmax _ hxB (by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, hxo, pow_one])
      have hx1 : (x : R) ∈ M ⊓ P.subgroupOf R := ⟨hxM, hxP⟩
      rw [disjoint_iff.mp hMdisj, mem_bot] at hx1
      have : orderOf (x : R) = 1 := by rw [hx1, orderOf_one]
      have e2 : orderOf (x : R) = orderOf x := Subgroup.orderOf_coe _
      rw [e2, hx] at this
      exact (Fact.out : ℓ.Prime).one_lt.ne' this)
  exact exists_normal_complement_of_subgroupOf hBR hM'n hM'

end LocalData

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
  CFSG.Semidihedral.StationaryConfinement in
theorem odd_subgroup_core_normal_complement
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 9 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} = ⊥)
    (R : Subgroup G) (hR : Odd (Nat.card R)) (hBR : (N t).map (C t).subtype ≤ R) :
    ∃ M : Subgroup G, M ≤ R ∧ R ≤ Subgroup.normalizer (M : Set G) ∧
      Disjoint M ((N t).map (C t).subtype) ∧ M ⊔ (N t).map (C t).subtype = R ∧
      Nat.card M * Nat.card ((N t).map (C t).subtype) = Nat.card R := by
  obtain ⟨J, d, hL, -⟩ := trivial_fixed_core_local_data G hGnonab hrecognition n hn S fS t ht
    hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov hY hA₀
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  obtain ⟨-, hconf, -, -⟩ :=
    stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element
      G hGnonab hrecognition n hn S fS t (fS (s n)) ht2 hs2 hsC hst.symm hnonab hcentral hnc p f
      hp hpodd hf (by omega) hmodel hcov
  have hBodd : Odd (Nat.card ((N t).map (C t).subtype)) := by
    rw [Subgroup.card_map_of_injective (C t).subtype_injective]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have hBnormal : (((N t).map (C t).subtype).subgroupOf (C t)).Normal :=
    ⟨fun x hx c => hL.B_conj c c.2 x hx⟩
  obtain ⟨hloc, -⟩ :=
    Principal.confined_normal_inverted_odd_subgroup_primes_do_not_divide_centralizer_index n hn S
      fS t ht _ (map_subtype_le _) hBodd hBnormal hL.s_inv hconf
  exact hL.odd_normal_complement hconf
    (fun ℓ hℓ hℓB P Q hQC hQp hPQ => (hloc ℓ hℓ hℓB P).1 Q hQC hQp hPQ) hR hBR

end CFSG.Semidihedral.FixedCoreNontrivial
