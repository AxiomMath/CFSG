module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Ex
public import CFSG.ClassicalInvolution.Asc77.AscT7ABasic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinUActsPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G]

omit [Group G] in
theorem card_sup_mul_card_inf_of_normal {G : Type*} [Group G] (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

omit [Group G] in
theorem card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem natCard_isSylow2In [Finite G] {V P : Subgroup G} (h : IsSylow2In V P) :
    Nat.card V = 2 ^ (Nat.card P).factorization 2 :=
  CFSG.ClassicalInvolution.Asc77.AscL62.natCard_eq_pow_of_isSylow2In h

theorem isPGroup_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    IsPGroup 2 ↥(Subgroup.closure ({a, b} : Set G)) := by
  have hcomm : IsMulCommutative (Subgroup.closure ({a, b} : Set G)) :=
    Subgroup.isMulCommutative_closure (by
      intro x hx y hy _
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact Commute.refl _
      · rw [Set.mem_singleton_iff.mp hy]; exact hab
      · rw [Set.mem_singleton_iff.mp hx]; exact hab.symm
      · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
  have hsq : ∀ x ∈ Subgroup.closure ({a, b} : Set G), x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact ha
      · rw [Set.mem_singleton_iff.mp hy]; exact hb
    | one => simp
    | mul y z hy' hz' hy hz =>
      have hc : y * z = z * y := by
        have h := hcomm.is_comm.comm (⟨y, hy'⟩ : Subgroup.closure ({a, b} : Set G)) ⟨z, hz'⟩
        exact congrArg Subtype.val h
      calc y * z * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [← hc]
        _ = (y * y) * (z * z) := by group
        _ = 1 := by rw [hy, hz, one_mul]
    | inv y _ hy =>
      calc y⁻¹ * y⁻¹ = (y * y)⁻¹ := by group
        _ = 1 := by rw [hy, inv_one]
  exact fun x => ⟨1, by apply Subtype.ext; simpa [sq] using hsq x x.2⟩

theorem mem_normalizer_of_comm_mem {N : Subgroup G} {x : G} (h1 : ∀ l ∈ N, ⁅x, l⁆ ∈ N)
    (h2 : ∀ l ∈ N, ⁅x⁻¹, l⁆ ∈ N) : x ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    have : x * l * x⁻¹ = ⁅x, l⁆ * l := by simp only [commutatorElement_def]; group
    rw [this]
    exact N.mul_mem (h1 l hl) hl
  · intro hl
    have h3 : ⁅x⁻¹, x * l * x⁻¹⁆ ∈ N := h2 _ hl
    have : x⁻¹ * (x * l * x⁻¹) * x⁻¹⁻¹ = l := by group
    have h4 : x⁻¹ * (x * l * x⁻¹) * x⁻¹⁻¹ = ⁅x⁻¹, x * l * x⁻¹⁆ * (x * l * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [← this, h4]
    exact N.mul_mem h3 hl

theorem cent_of_normalizer {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) {r : G}
    (hr : r ∈ Subgroup.normalizer (K : Set G)) : r * z = z * r := by
  have h1 : r * z * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hr z).mp hz.mem
  have h2 : (r * z * r⁻¹) * (r * z * r⁻¹) = 1 := by
    calc (r * z * r⁻¹) * (r * z * r⁻¹) = r * (z * z) * r⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rcases hz.unique _ h1 h2 with h | h
  · exfalso
    apply hz.ne_one
    have : z = r⁻¹ * (r * z * r⁻¹) * r := by group
    rw [this, h]
    group
  · calc r * z = r * z * r⁻¹ * r := by group
      _ = z * r := by rw [h]

theorem le_centralizerModOdd_of_comm (A J : Subgroup G)
    (h : ∀ x ∈ A, ∀ l ∈ J, ⁅x, l⁆ ∈ oddCoreOf J) : A ≤ centralizerModOdd ⊤ J := by
  have hO : oddCoreOf J ≤ J := Subgroup.map_subtype_le _
  intro x hx
  have hx' : x⁻¹ ∈ A := A.inv_mem hx
  refine ⟨Subgroup.mem_top x, ?_, ?_, h x hx⟩
  · exact mem_normalizer_of_comm_mem (fun l hl => hO (h x hx l hl))
      (fun l hl => hO (h x⁻¹ hx' l hl))
  · exact mem_normalizer_of_comm_mem (fun l hl => h x hx l (hO hl))
      (fun l hl => h x⁻¹ hx' l (hO hl))

section Six

variable [Finite G] {Ω : Set (Subgroup G)}

theorem comm_of_sylow (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z t : G}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hzt : z ≠ t) {V : Subgroup G}
    (hV : IsSylow2In V J) (hVz : V ≤ Subgroup.centralizer ({z} : Set G)) :
    ∀ v ∈ V, ∀ k ∈ K, ⁅v, k⁆ ∈ oddCoreOf K := by
  have hV' : IsSylow2In V (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    ⟨le_inf hV.1 hVz, hV.2.1, fun V' hV'P hV'2 hle => hV.2.2 V' (hV'P.trans inf_le_left) hV'2 hle⟩
  have htV : t ∈ V := Sec6Gen.mem_of_isSylow2In ht hV
  have hJnt : J ∉ twinSet Ω K := by
    rintro ⟨-, z', hz', hz'J⟩
    exact hzt ((hz.eq hz').trans (hz'J.eq ht))
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ hV)).exists_not_commute
  rcases Sec6Gen.l6_2Gen G Ω hΩ K hK z hz J hJ hJnt t ht V hV' htV with h | h | h | h
  · exfalso
    rw [h.1] at hx hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hxy ((Commute.zpow_zpow_self t m n).eq)
  · exfalso
    rw [h.1] at hx hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hxy ((Commute.zpow_zpow_self t m n).eq)
  · exfalso
    obtain ⟨R, -, -, hcyc, -⟩ := h.1
    exact hxy (AscL62.cyclic_comm hcyc hx hy)
  · exact fun v hv k hk => h.2 (Subgroup.commutator_mem_commutator hv hk)

end Six

section Frame

variable [Finite G] {Ω : Set (Subgroup G)} {K K' J : Subgroup G} {z u t : G}

theorem t_acts (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z ≠ t) (hJK : J ∈ omegaNbr Ω K) :
    t ∈ Subgroup.normalizer (K : Set G) ∧ ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K := by
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := hJK
  have hRs : IsSylow2In R J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJ hR hRJ
  have htR : t ∈ R := Sec6Gen.mem_of_isSylow2In ht hRs
  have hRc : R ≤ Subgroup.centralizer ({z} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (cent_of_normalizer hz (hRN hr))
  exact ⟨hRN htR, comm_of_sylow hΩ hK hJ hz ht hzt hRs hRc t htR⟩

theorem comm_twin (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K ≠ K')
    (hzK : IsUniqueInvolution K z) (hzK' : IsUniqueInvolution K' z) :
    K' ≤ Subgroup.normalizer (K : Set G) ∧ K ≤ Subgroup.normalizer (K' : Set G) := by
  have hc := Sec6Gen.comm_le_oddCore_of_twin hΩ hK hK' hne hzK hzK'
  have hOK : oddCoreOf K ≤ K := Subgroup.map_subtype_le _
  have hOK' : oddCoreOf K' ≤ K' := Subgroup.map_subtype_le _
  have h1 : ∀ a ∈ K, ∀ b ∈ K', ⁅a, b⁆ ∈ K ∧ ⁅a, b⁆ ∈ K' := fun a ha b hb =>
    ⟨hOK (hc (Subgroup.commutator_mem_commutator ha hb)).1,
      hOK' (hc (Subgroup.commutator_mem_commutator ha hb)).2⟩
  have h2 : ∀ a ∈ K, ∀ b ∈ K', ⁅b, a⁆ ∈ K ∧ ⁅b, a⁆ ∈ K' := fun a ha b hb => by
    rw [← commutatorElement_inv]
    exact ⟨K.inv_mem (h1 a ha b hb).1, K'.inv_mem (h1 a ha b hb).2⟩
  constructor
  · intro b hb
    exact mem_normalizer_of_comm_mem (fun l hl => (h2 l hl b hb).1)
      (fun l hl => (h2 l hl b⁻¹ (K'.inv_mem hb)).1)
  · intro a ha
    exact mem_normalizer_of_comm_mem (fun l hl => (h1 a ha l hl).2)
      (fun l hl => (h1 a⁻¹ (K.inv_mem ha) l hl).2)

theorem inf_sup_le {K K' Q : Subgroup G} (hKK' : K' ≤ Subgroup.normalizer (K : Set G))
    (hQ : IsPGroup 2 Q) (hA : IsSylow2In (Q ⊓ K) K) (hB : IsSylow2In (Q ⊓ K') K')
    (hinf : 2 ∣ Nat.card ↥(K ⊓ K')) (hAB : Nat.card ↥((Q ⊓ K) ⊓ (Q ⊓ K')) ≤ 2) :
    Q ⊓ (K ⊔ K') ≤ (Q ⊓ K) ⊔ (Q ⊓ K') := by
  set A := Q ⊓ K with hAdef
  set B := Q ⊓ K' with hBdef
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have hbK : b ∈ Subgroup.normalizer (K : Set G) := hKK' hb.2
    simp only [hAdef, Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp hbK a]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨Q.mul_mem (Q.mul_mem hb.1 h1) (Q.inv_mem hb.1), h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have := Q.mul_mem (Q.mul_mem (Q.inv_mem hb.1) h1) hb.1
      have e : b⁻¹ * (b * a * b⁻¹) * b = a := by group
      rwa [e] at this
  have hAB' := card_sup_mul_card_inf_of_le_normalizer hBA
  have hX := card_sup_mul_card_inf_of_le_normalizer hKK'
  have hAle : A ≤ Q ⊓ (K ⊔ K') := le_inf inf_le_left (inf_le_right.trans le_sup_left)
  have hBle : B ≤ Q ⊓ (K ⊔ K') := le_inf inf_le_left (inf_le_right.trans le_sup_right)
  have hle : A ⊔ B ≤ Q ⊓ (K ⊔ K') := sup_le hAle hBle
  obtain ⟨V, hV, hQV⟩ := IsSylow2In.exists_ge (P := K ⊔ K') (T := Q ⊓ (K ⊔ K'))
    (hQ.to_le inf_le_left) inf_le_right
  have hQX : Nat.card ↥(Q ⊓ (K ⊔ K')) ≤ 2 ^ (Nat.card ↥(K ⊔ K')).factorization 2 := by
    rw [← natCard_isSylow2In hV]
    exact Subgroup.card_le_of_le hQV
  have hKne : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hK'ne : Nat.card K' ≠ 0 := Nat.card_pos.ne'
  have hXne : Nat.card ↥(K ⊔ K') ≠ 0 := Nat.card_pos.ne'
  have hIne : Nat.card ↥(K ⊓ K') ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card ↥(K ⊔ K')).factorization 2 + (Nat.card ↥(K ⊓ K')).factorization 2 =
      (Nat.card K).factorization 2 + (Nat.card K').factorization 2 := by
    have := congrArg (fun n => n.factorization 2) hX
    rw [Nat.factorization_mul hXne hIne, Nat.factorization_mul hKne hK'ne] at this
    simpa using this
  have hpos : 1 ≤ (Nat.card ↥(K ⊓ K')).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hIne hinf
  have hcardAB : Nat.card A * Nat.card B =
      2 ^ (Nat.card ↥(K ⊔ K')).factorization 2 * 2 ^ (Nat.card ↥(K ⊓ K')).factorization 2 := by
    rw [natCard_isSylow2In hA, natCard_isSylow2In hB, ← pow_add, ← pow_add, hfac]
  have h2le : 2 ≤ 2 ^ (Nat.card ↥(K ⊓ K')).factorization 2 := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hpos
  have hmain : Nat.card ↥(Q ⊓ (K ⊔ K')) * 2 ≤ Nat.card ↥(A ⊔ B) * 2 := by
    calc Nat.card ↥(Q ⊓ (K ⊔ K')) * 2
        ≤ 2 ^ (Nat.card ↥(K ⊔ K')).factorization 2 * 2 ^ (Nat.card ↥(K ⊓ K')).factorization 2 :=
          Nat.mul_le_mul hQX h2le
      _ = Nat.card A * Nat.card B := hcardAB.symm
      _ = Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := hAB'.symm
      _ ≤ Nat.card ↥(A ⊔ B) * 2 := Nat.mul_le_mul_left _ hAB
  have hcard : Nat.card ↥(Q ⊓ (K ⊔ K')) ≤ Nat.card ↥(A ⊔ B) := Nat.le_of_mul_le_mul_right hmain
    (by norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm.le

theorem twinFrame_u_mem_centralizerModOdd (hΩ : HypOmegaGen Ω)
    (hf : Asc77.TwinFrameData Ω K K' z u J t) : u ∈ centralizerModOdd ⊤ J := by
  have hK : K ∈ Ω := hf.mem
  have hK'Ω : K' ∈ Ω := hf.hK'.1
  have hJΩ : J ∈ Ω := hf.hJ.1
  have hzK' : IsUniqueInvolution K' z := by
    obtain ⟨-, z', hz', hz'K'⟩ := hf.hK'
    exact (hf.hz.eq hz') ▸ hz'K'
  have hne : K ≠ K' := hf.hne.symm
  have hzt : z ≠ t := hf.t_ne_z.symm
  have hJK : J ∈ omegaNbr Ω K := hf.hJ.2 K ⟨hK, z, hf.hz, hf.hz⟩
  have hJK' : J ∈ omegaNbr Ω K' := hf.hJ.2 K' hf.hK'
  obtain ⟨htK, htcK⟩ := t_acts hΩ hK hJΩ hf.hz hf.ht hzt hJK
  obtain ⟨htK', htcK'⟩ := t_acts hΩ hK'Ω hJΩ hzK' hf.ht hzt hJK'
  obtain ⟨hK'N, hKN⟩ := comm_twin hΩ hK hK'Ω hne hf.hz hzK'
  set H : Subgroup G := (K ⊔ K') ⊔ Subgroup.zpowers t with hH
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hK'N) (Subgroup.zpowers_le.mpr htK)
  have hHK' : H ≤ Subgroup.normalizer (K' : Set G) :=
    sup_le (sup_le hKN Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr htK')
  have hKH : K ≤ H := le_sup_left.trans le_sup_left
  have hK'H : K' ≤ H := le_sup_right.trans le_sup_left
  have htH : t ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have huH : u ∈ H := Subgroup.mem_sup_left hf.hu
  have hT2 := isPGroup_closure_pair hf.ht.sq hf.hu2 hf.htu
  have hTH : Subgroup.closure ({t, u} : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact htH
    · rw [Set.mem_singleton_iff.mp hx]; exact huH
  obtain ⟨Q, hQ, hTQ⟩ := IsSylow2In.exists_ge hT2 hTH
  have htQ : t ∈ Q := hTQ (Subgroup.subset_closure (Or.inl rfl))
  have huQ : u ∈ Q := hTQ (Subgroup.subset_closure (Or.inr rfl))
  have hA : IsSylow2In (Q ⊓ K) K := Sec6Gen.isSylow2In_inf_of_le_normalizer' hQ hKH hHK
  have hB : IsSylow2In (Q ⊓ K') K' := Sec6Gen.isSylow2In_inf_of_le_normalizer' hQ hK'H hHK'
  have hcent : ∀ {M : Subgroup G}, (∀ k ∈ M, ⁅t, k⁆ ∈ oddCoreOf M) → ∀ a ∈ Q ⊓ M,
      a * t = t * a := by
    intro M hM a ha
    have h1 : ⁅t, a⁆ ∈ oddCoreOf M := hM a ha.2
    have h2 : ⁅t, a⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem htQ ha.1) (Q.inv_mem htQ)) (Q.inv_mem ha.1)
    have h3 : ⁅t, a⁆ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard M) h1
        (hQ.2.1.to_le (Subgroup.zpowers_le.mpr h2))
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  have hAc : Q ⊓ K ≤ Subgroup.centralizer ({t} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcent htcK a ha)
  have hBc : Q ⊓ K' ≤ Subgroup.centralizer ({t} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcent htcK' a ha)
  have hAJ : Q ⊓ K ≤ centralizerModOdd ⊤ J :=
    le_centralizerModOdd_of_comm _ J
      (comm_of_sylow hΩ hJΩ hK hf.ht hf.hz hzt.symm hA hAc)
  have hBJ : Q ⊓ K' ≤ centralizerModOdd ⊤ J :=
    le_centralizerModOdd_of_comm _ J
      (comm_of_sylow hΩ hJΩ hK'Ω hf.ht hzK' hzt.symm hB hBc)
  have hz2 : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hf.hz.sq) hf.hz.ne_one
  have hinf : 2 ∣ Nat.card ↥(K ⊓ K') := by
    have := Subgroup.orderOf_dvd_natCard (K ⊓ K') (x := z) ⟨hf.hz.mem, hzK'.mem⟩
    rwa [hz2] at this
  have hAB : Nat.card ↥((Q ⊓ K) ⊓ (Q ⊓ K')) ≤ 2 :=
    Sec6Gen.card_le_two_of_le_inf hΩ hK hK'Ω hne
      (hQ.2.1.to_le ((inf_le_left.trans inf_le_left)))
      (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have hu : u ∈ Q ⊓ (K ⊔ K') := ⟨huQ, hf.hu⟩
  exact (sup_le hAJ hBJ) (inf_sup_le hK'N hQ.2.1 hA hB hinf hAB hu)

end Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinUActsPf

end
