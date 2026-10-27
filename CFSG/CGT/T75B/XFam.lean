module

public import CFSG.CGT.T75B.FamSet
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJBasic

public section

namespace CFSG.CGT.T75B

open CFSG.Open CFSG.CGT.Timmesfeld75

section Comm

variable {G : Type} [Group G]

theorem comm_conj_of_involution {N : Subgroup G} (hN : IsElemAbelian 2 N) {x : G}
    (hxx : x * x = 1) (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) {n n' : G} (hn : n ∈ N) (hn' : n' ∈ N) :
    (n * x * n⁻¹) * (n' * x * n'⁻¹) = (n' * x * n'⁻¹) * (n * x * n⁻¹) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hμ : ∀ m ∈ N, m * (x * m⁻¹ * x⁻¹) ∈ N ∧ x * (m * (x * m⁻¹ * x⁻¹)) = (m * (x * m⁻¹ * x⁻¹)) * x := by
    intro m hm
    have h1 : m * (x * m⁻¹ * x⁻¹) ∈ N := N.mul_mem hm (hxN _ (N.inv_mem hm))
    refine ⟨h1, ?_⟩
    have hsq : (m * (x * m⁻¹ * x⁻¹)) * (m * (x * m⁻¹ * x⁻¹)) = 1 := elemAbelian_mul_self hN h1
    have hinv : (m * (x * m⁻¹ * x⁻¹))⁻¹ = m * (x * m⁻¹ * x⁻¹) := inv_eq_of_mul_eq_one_right hsq
    have e : x * (m * (x * m⁻¹ * x⁻¹)) * x⁻¹ = (m * (x * m⁻¹ * x⁻¹))⁻¹ := by
      have e1 : x * (m * (x * m⁻¹ * x⁻¹)) * x⁻¹ = (x * m * x⁻¹) * ((x * x) * m⁻¹ * (x * x)⁻¹) := by
        group
      rw [e1, hxx]
      group
    rw [hinv] at e
    calc x * (m * (x * m⁻¹ * x⁻¹)) = (x * (m * (x * m⁻¹ * x⁻¹)) * x⁻¹) * x := by group
      _ = (m * (x * m⁻¹ * x⁻¹)) * x := by rw [e]
  obtain ⟨hμn, hxμn⟩ := hμ n hn
  obtain ⟨hμn', hxμn'⟩ := hμ n' hn'
  set μ := n * (x * n⁻¹ * x⁻¹) with hμdef
  set μ' := n' * (x * n'⁻¹ * x⁻¹) with hμ'def
  have e1 : n * x * n⁻¹ = μ * x := by rw [hμdef]; group
  have e2 : n' * x * n'⁻¹ = μ' * x := by rw [hμ'def]; group
  have hμμ' : μ * μ' = μ' * μ := elemAbelian_mul_comm hN hμn hμn'
  rw [e1, e2]
  calc μ * x * (μ' * x) = μ * (x * μ') * x := by group
    _ = μ * (μ' * x) * x := by rw [hxμn']
    _ = (μ * μ') * (x * x) := by group
    _ = μ * μ' := by rw [hxx, mul_one]
    _ = μ' * μ := hμμ'
    _ = (μ' * μ) * (x * x) := by rw [hxx, mul_one]
    _ = μ' * (μ * x) * x := by group
    _ = μ' * (x * μ) * x := by rw [hxμn]
    _ = μ' * x * (μ * x) := by group

end Comm

section Fam

variable {G : Type} [Group G]

@[expose] def xFam (T T₁ Tx N : Subgroup G) : Set (Subgroup G) :=
  {T, T₁} ∪ {U | ∃ n ∈ N, U = conjSubgroup n Tx}

theorem mem_xFam {T T₁ Tx N M : Subgroup G} :
    M ∈ xFam T T₁ Tx N ↔ M = T ∨ M = T₁ ∨ ∃ n ∈ N, M = conjSubgroup n Tx := by
  simp [xFam, or_assoc]

end Fam

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {T T₁ T₂ : Subgroup G} {a : G}

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.exists_big_F
    (h : Sec4Hyp T T₁ a T₂) (hnab : ∃ a b : G, a * b ≠ b * a) (h16 : Nat.card T ≠ 16)
    (hL : 16 ≤ Nat.card (normIn T T₁)) {x : G}
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) (hx₁ : x ∈ Subgroup.normalizer (T₁ : Set G))
    (hxN : x ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) (hxnT : x ∉ T)
    {Tx : Subgroup G} (hTx : ∃ g : G, Tx = conjSubgroup g T) (hxTx : x ∈ Tx) :
    ∃ F : Subgroup G, F ≤ Tx ∧ 4 ≤ Nat.card F ∧
      (∀ f ∈ F, f ∈ Subgroup.normalizer (T : Set G) ∧ f ∈ Subgroup.normalizer (T₁ : Set G)) ∧
      (∀ f ∈ F, ∀ y ∈ sec4N T T₁ T₂, f * (y * f * y⁻¹) = (y * f * y⁻¹) * f) := by
  classical
  set N := sec4N T T₁ T₂ with hNdef
  have hNab : IsElemAbelian 2 N := h.isElemAbelian_sec4N
  have hTab : IsElemAbelian 2 T := h.pair.wc.1
  obtain ⟨g, hg⟩ := hTx
  have hTxWC : IsWC Tx := hg ▸ h.pair.wc.conj g
  have hxx : x * x = 1 := elemAbelian_mul_self hTxWC.1 hxTx
  have hx1 : x ≠ 1 := fun h1 => hxnT (h1 ▸ T.one_mem)
  have hTxne : Tx ≠ T := fun h' => hxnT (h' ▸ hxTx)
  have hNT : N ≤ Subgroup.normalizer (T : Set G) := sec4N_le_normalizer_left
  have hNT₁ : N ≤ Subgroup.normalizer (T₁ : Set G) := h.sec4N_le_normalizer_mid
  have hxN' : ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun n hn => (Subgroup.mem_normalizer_iff.1 hxN n).1 hn
  have hcomm_n : ∀ n ∈ N, ∀ n' ∈ N,
      (n * x * n⁻¹) * (n' * x * n'⁻¹) = (n' * x * n'⁻¹) * (n * x * n⁻¹) :=
    fun n hn n' hn' => comm_conj_of_involution hNab hxx hxN' hn hn'
  have hxn_ne : ∀ n : G, n * x * n⁻¹ ≠ 1 := fun n h1 => hx1 (by
    have : x = n⁻¹ * (n * x * n⁻¹) * n := by group
    rw [this, h1]; group)
  have hnormTxn : ∀ n ∈ N, ∀ u : G, u * (n * x * n⁻¹) = (n * x * n⁻¹) * u →
      u ∈ Subgroup.normalizer (conjSubgroup n Tx : Set G) := fun n _ u hu =>
    (hTxWC.conj n).centralizer_le_normalizer (conj_mem_conjSubgroup n hxTx) (hxn_ne n)
      (Subgroup.mem_centralizer_singleton_iff.2 hu)
  set S : Set (Subgroup G) := xFam T T₁ Tx N with hSdef
  have hTS : T ∈ S := mem_xFam.2 (Or.inl rfl)
  have hT₁S : T₁ ∈ S := mem_xFam.2 (Or.inr (Or.inl rfl))
  have hconjS : ∀ n ∈ N, conjSubgroup n Tx ∈ S := fun n hn => mem_xFam.2 (Or.inr (Or.inr ⟨n, hn, rfl⟩))
  have hTxS : Tx ∈ S := by
    have := hconjS 1 N.one_mem
    rwa [conjSubgroup_one] at this
  have hSne : S.Nonempty := ⟨T, hTS⟩
  have hclosed : ∀ y ∈ N, ∀ M ∈ S, conjSubgroup y M ∈ S := by
    intro y hy M hM
    rcases mem_xFam.1 hM with rfl | rfl | ⟨n, hn, rfl⟩
    · rw [mem_normalizer_iff_conjSubgroup_eq.1 (hNT hy)]; exact hTS
    · rw [mem_normalizer_iff_conjSubgroup_eq.1 (hNT₁ hy)]; exact hT₁S
    · rw [conjSubgroup_conjSubgroup]; exact hconjS _ (N.mul_mem hy hn)
  have hnormS : ∀ u ∈ N, x * u = u * x → ∀ M ∈ S, u ∈ Subgroup.normalizer (M : Set G) := by
    intro u hu hxu M hM
    rcases mem_xFam.1 hM with rfl | rfl | ⟨n, hn, rfl⟩
    · exact hNT hu
    · exact hNT₁ hu
    · refine hnormTxn n hn u ?_
      have hun : u * n = n * u := elemAbelian_mul_comm hNab hu hn
      have hun' : u * n⁻¹ = n⁻¹ * u := elemAbelian_mul_comm hNab hu (N.inv_mem hn)
      calc u * (n * x * n⁻¹) = (u * n) * x * n⁻¹ := by group
        _ = n * (u * x) * n⁻¹ := by rw [hun]; group
        _ = n * (x * u) * n⁻¹ := by rw [hxu]
        _ = n * x * (u * n⁻¹) := by group
        _ = n * x * (n⁻¹ * u) := by rw [hun']
        _ = (n * x * n⁻¹) * u := by group
  have hxnormS : ∀ n ∈ N, ∀ M ∈ S, n * x * n⁻¹ ∈ Subgroup.normalizer (M : Set G) := by
    intro n₀ hn₀ M hM
    rcases mem_xFam.1 hM with rfl | rfl | ⟨n, hn, rfl⟩
    · exact (Subgroup.normalizer (M : Set G)).mul_mem
        ((Subgroup.normalizer (M : Set G)).mul_mem (hNT hn₀) hxT)
        ((Subgroup.normalizer (M : Set G)).inv_mem (hNT hn₀))
    · exact (Subgroup.normalizer (M : Set G)).mul_mem
        ((Subgroup.normalizer (M : Set G)).mul_mem (hNT₁ hn₀) hx₁)
        ((Subgroup.normalizer (M : Set G)).inv_mem (hNT₁ hn₀))
    · exact hnormTxn n hn _ (hcomm_n n₀ hn₀ n hn)
  have hxL : ∀ v ∈ normIn T T₁, x * v * x⁻¹ ∈ normIn T T₁ := fun v hv => by
    have := conj_mem_conjSubgroup x hv
    rwa [conjSubgroup_normIn_eq_of_mem_normalizer hxT hx₁] at this
  have hxL₁ : ∀ v ∈ normIn T₁ T, x * v * x⁻¹ ∈ normIn T₁ T := fun v hv => by
    have := conj_mem_conjSubgroup x hv
    rwa [conjSubgroup_normIn_eq_of_mem_normalizer hx₁ hxT] at this
  obtain ⟨u₀, hu₀L, hu₀1, hxu₀⟩ := exists_ne_one_mem_centralizer_of_involution
    (isElemAbelian_of_le hTab (normIn_le T T₁)) h.sec3.cfg.ne hxx hxL
  obtain ⟨u₁, hu₁L, hu₁1, hxu₁⟩ := exists_ne_one_mem_centralizer_of_involution
    (isElemAbelian_of_le h.isWC₁.1 (normIn_le T₁ T)) h.sec3.cfg.ne₁ hxx hxL₁
  have hu₀N : u₀ ∈ N := normIn_le_sec4N_left hu₀L
  have hu₁N : u₁ ∈ N := normIn_le_sec4N_mid hu₁L
  have hne : ∀ A ∈ S, famFS S A ≠ ⊥ := by
    intro A hA
    rcases mem_xFam.1 hA with rfl | rfl | ⟨n, hn, rfl⟩
    · exact Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨u₀, (mem_famFS_iff hSne).2
        ⟨normIn_le _ _ hu₀L, hnormS u₀ hu₀N hxu₀⟩⟩, fun h' => hu₀1 (congrArg Subtype.val h')⟩
    · exact Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨u₁, (mem_famFS_iff hSne).2
        ⟨normIn_le _ _ hu₁L, hnormS u₁ hu₁N hxu₁⟩⟩, fun h' => hu₁1 (congrArg Subtype.val h')⟩
    · exact Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨n * x * n⁻¹, (mem_famFS_iff hSne).2
        ⟨conj_mem_conjSubgroup n hxTx, hxnormS n hn⟩⟩, fun h' => hxn_ne n (congrArg Subtype.val h')⟩
  have hconj : ∀ M ∈ S, ∃ k : G, M = conjSubgroup k T := by
    intro M hM
    rcases mem_xFam.1 hM with rfl | rfl | ⟨n, hn, rfl⟩
    · exact ⟨1, (conjSubgroup_one _).symm⟩
    · exact h.pair.conj
    · exact ⟨n * g, by rw [hg, conjSubgroup_conjSubgroup]⟩
  obtain ⟨hQ, hQn⟩ := cfg313_of_set hnab h.pair.wc h.glob h.iso h16 hTS hconj hne
  set Q : Subgroup G := ⨆ A ∈ S, famFS S A with hQdef
  set R : Subgroup G := ⨆ M ∈ S, M with hRdef
  have hQN : ∀ M ∈ S, Q ≤ Subgroup.normalizer (M : Set G) := fun M hM =>
    iSup₂_le fun A _ v hv => mem_normalizer_of_mem_famFS hv hM
  have hfam : ∀ A ∈ S, famFS S A = Q ⊓ A := by
    intro A hA
    ext u
    constructor
    · intro hu
      exact ⟨(le_iSup₂ (f := fun A (_ : A ∈ S) => famFS S A) A hA) hu, famFS_le hA hu⟩
    · rintro ⟨huQ, huA⟩
      exact (mem_famFS_iff hSne).2 ⟨huA, fun M hM => hQN M hM huQ⟩
  refine ⟨famFS S Tx, famFS_le hTxS, ?_, fun f hf =>
    ⟨mem_normalizer_of_mem_famFS hf hTS, mem_normalizer_of_mem_famFS hf hT₁S⟩, ?_⟩
  ·
    have hsq := card_le_sq_centralizer (isElemAbelian_of_le hTab (normIn_le T T₁)) hxx hxL
    have hC4 : 4 ≤ Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({x} : Set G)) := by
      by_contra hlt
      have h3 : Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 3 := by omega
      have : Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({x} : Set G)) ^ 2 ≤ 9 := by nlinarith
      omega
    have hCle : normIn T T₁ ⊓ Subgroup.centralizer ({x} : Set G) ≤ famFS S T := by
      intro u hu
      refine (mem_famFS_iff hSne).2 ⟨normIn_le _ _ hu.1, fun M hM => hnormS u
        (normIn_le_sec4N_left hu.1) ?_ M hM⟩
      exact (Subgroup.mem_centralizer_singleton_iff.1 hu.2).symm
    have hu₀Tx : u₀ ∈ normIn T Tx := mem_normIn.2 ⟨normIn_le _ _ hu₀L, hnormS u₀ hu₀N hxu₀ Tx hTxS⟩
    have hLTx : normIn T Tx ≠ ⊥ := Subgroup.ne_bot_iff_exists_ne_one.2
      ⟨⟨u₀, hu₀Tx⟩, fun h' => hu₀1 (congrArg Subtype.val h')⟩
    have hS3 : Sec3 T Tx :=
      sec3_of_conj_conj h.glob ⟨1, (conjSubgroup_one T).symm⟩ ⟨g, hg⟩ hTxne hLTx
    obtain ⟨y, hy, hy'⟩ := hS3.conj
    have hyR : y ∈ R := sup_le (le_iSup₂ (f := fun M (_ : M ∈ S) => M) T hTS)
      (le_iSup₂ (f := fun M (_ : M ∈ S) => M) Tx hTxS) hy
    have hcard : Nat.card ↥(Q ⊓ Tx) = Nat.card ↥(Q ⊓ T) := by
      have e : Q ⊓ Tx = conjSubgroup y (Q ⊓ T) := by
        rw [conjSubgroup_inf, hQn y hyR, ← hy']
      rw [e, card_conjSubgroup]
    calc 4 ≤ Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({x} : Set G)) := hC4
      _ ≤ Nat.card ↥(famFS S T) := Subgroup.card_le_of_le hCle
      _ = Nat.card ↥(Q ⊓ T) := by rw [hfam T hTS]
      _ = Nat.card ↥(Q ⊓ Tx) := hcard.symm
      _ = Nat.card ↥(famFS S Tx) := by rw [hfam Tx hTxS]
  ·
    intro f hf y hy
    have hfQ : f ∈ Q := ((hfam Tx hTxS) ▸ hf : f ∈ Q ⊓ Tx).1
    have hyf : y * f * y⁻¹ ∈ famFS S (conjSubgroup y Tx) := by
      refine (mem_famFS_iff hSne).2 ⟨conj_mem_conjSubgroup y (famFS_le hTxS hf), fun M hM => ?_⟩
      have hM' : conjSubgroup y⁻¹ M ∈ S := hclosed y⁻¹ (N.inv_mem hy) M hM
      have hfM' := mem_normalizer_of_mem_famFS hf hM'
      have e : conjSubgroup y (conjSubgroup y⁻¹ M) = M := by
        rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      rw [← e, mem_normalizer_conjSubgroup_iff]
      simpa [mul_assoc] using hfM'
    have hyfQ : y * f * y⁻¹ ∈ Q :=
      (le_iSup₂ (f := fun A (_ : A ∈ S) => famFS S A) (conjSubgroup y Tx) (hconjS y hy)) hyf
    exact elemAbelian_mul_comm hQ hfQ hyfQ

end Main

end CFSG.CGT.T75B
